//! The pool's own workers: one thread for each token of the pool's width.
//!
//! **A hand-off writes the job into a worker's seat.** Each worker owns a seat
//! that holds one job reference. A reference is three words: the address of
//! the frame that holds the job, the part of the frame to run, and the
//! function that runs the part. A party takes the bit of an idle worker,
//! writes the reference into the worker's seat and wakes the worker. The
//! worker runs the part from the seat. So a hand-off allocates nothing, and
//! the job stays in its frame.
//!
//! **A party takes back each part that no worker started.** A party that
//! waits for its parts first takes back each part whose worker did not start
//! it. So a wait waits only for parts that run, and no fork waits for a worker
//! that no party frees.
//!
//! **A worker spins up to the cost of a park, then parks.** An idle worker
//! spins until a post comes or the host's park-to-wake cost passes. Then it
//! parks on its seat, and the party that writes its seat wakes it. So a post
//! within that cost costs no wake, and a longer gap costs at most twice a park
//! at once. A post goes first to a worker that spins. The pool measures the
//! cost at its start and keeps it as one number for each host and width, so no
//! constant sets the park.
//!
//! **A spawn that finds no idle worker waits in a queue.** A worker takes from
//! the queue before it parks, and a party that waits for a spawned job runs
//! queued jobs while it waits. The standing jobs of a session wait in a second
//! queue that only the workers take from.
//!
//! **A worker never unwinds.** Each frame catches the panic of its part and
//! keeps it for the party that waits. A part that unwinds all the same gives
//! its worker back to the pool.
//!
//! # References
//!
//! - `vault:01a1cf3f-b730-7152-9d64-050e5c00b32a` — anchor: the shared pool
//!   page, § pool-tokens: one token for each thread of the width, and a wait on
//!   a futex.

use alloc::collections::VecDeque;
use alloc::sync::Arc;
use core::any::Any;
use core::cell::Cell;
use core::cell::UnsafeCell;
use core::mem::MaybeUninit;
use core::num::NonZeroUsize;
use core::panic::AssertUnwindSafe;
use core::sync::atomic::AtomicBool;
use core::sync::atomic::AtomicU64;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
use core::sync::atomic::fence;
use core::time::Duration;
use std::path::Path;
use std::sync::Mutex;
use std::sync::MutexGuard;
use std::thread::Thread;
use std::time::Instant;

use quenchant_shape::shape::Maybe;

use super::Spin;
use super::lane::Sleeper;
use crate::width::Threads;

quenchant_shape::reason_enum! {
    /// Why no worker seat answers.
    pub mod unseated {
        /// The reason no worker takes the part, or the thread holds no seat.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Every worker holds a part of its own.
            Busy,
            /// The current thread is not one of the workers.
            Outside,
        }
    }
}

/// The place of one part in its frame.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Part(pub usize);

/// The place of one worker in its pool.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct WorkerIndex(pub usize);

/// How many parts of a fork went to a worker.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Posts(pub usize);

/// A frame whose parts a worker or the waiting party runs.
///
/// # Specification
/// - provides: the run of one part, which any thread may call while the frame
///   lives.
/// - panics: a panic of the part.
/// - executable: none — a seam between a fork's frame and the workers.
pub trait Runs: Sync
{
    /// Run the part `part` of the frame.
    ///
    /// # Specification
    /// trivial.
    fn run(
        &self,
        part: Part,
    );
}

/// What a party does with a part that it took back from a worker.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Back
{
    /// Run the part on the party's thread.
    Run,
    /// Drop the part: the party's own work covers what the part does.
    Drop,
}

/// Whether a party took a part back from its worker.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Retracted
{
    /// The worker did not start the part, and the party holds it again.
    Back,
    /// The worker started the part.
    Started,
}

/// Whether a party ran a job.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Helped
{
    /// It ran one job.
    Ran,
    /// No job waited for it.
    Idle,
}

/// The first panic of the parts of one fork or scope.
///
/// # Specification
/// - provides: the keep of a panic, of which only the first stays, and the
///   panic kept once the parts ended.
/// - panics: none.
/// - executable: none — a type-level block; [`Workers::fork`] carries the
///   obligations.
#[derive(Debug, Default)]
#[repr(transparent)]
pub struct FirstPanic(Mutex<Option<Box<dyn Any + Send>>>);

impl FirstPanic
{
    /// Keep `panic` unless a panic is kept already.
    ///
    /// # Specification
    /// trivial.
    pub fn keep(
        &self,
        panic: Box<dyn Any + Send>,
    )
    {
        let mut kept = match self.0.lock() {
            Ok(kept) => kept,
            Err(poisoned) => poisoned.into_inner(),
        };
        if kept.is_none() {
            *kept = Some(panic);
        }
    }

    /// Resume the kept panic, if any.
    ///
    /// # Specification
    /// trivial.
    pub fn resume(self)
    {
        let kept = match self.0.into_inner() {
            Ok(kept) => kept,
            Err(poisoned) => poisoned.into_inner(),
        };
        if let Some(panic) = kept {
            std::panic::resume_unwind(panic);
        }
    }
}

/// One part of a frame, as a worker's seat holds it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
pub struct JobRef
{
    /// The frame that holds the part.
    frame: *const (),
    /// The part of the frame.
    part: Part,
    /// The function that runs the part of a frame of the frame's type.
    run: unsafe fn(*const (), Part),
}

/// A job reference names a frame that is `Sync`, or a frame that a reference
/// count keeps.
///
/// # Safety
/// - unsafe invariants: [`JobRef::of`] takes only a `Sync` frame, and
///   [`JobRef::new`] makes its caller state that the frame may move to another
///   thread.
// SAFETY: `JobRef::of` takes only a `Sync` frame, so its part runs on any
// thread. `JobRef::new` puts the same obligation on its caller.
unsafe impl Send for JobRef
{
}

impl JobRef
{
    /// The part `part` of `frame`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn of<Frame>(
        frame: &Frame,
        part: Part,
    ) -> Self
    where
        Frame: Runs,
    {
        Self {
            frame: core::ptr::from_ref(frame).cast(),
            part,
            run: run_frame::<Frame>,
        }
    }

    /// The part `part` of the frame at `frame`, which `run` runs.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Safety
    /// - requires: `run` may run `part` of `frame` on any thread, once, while
    ///   the reference is in a seat or a queue.
    #[inline]
    #[must_use]
    pub const unsafe fn new(
        frame: *const (),
        part: Part,
        run: unsafe fn(*const (), Part),
    ) -> Self
    {
        Self { frame, part, run }
    }

    /// Run the part.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Safety
    /// - requires: the frame lives until the call returns.
    #[inline]
    unsafe fn execute(self)
    {
        // SAFETY: the caller keeps the frame alive, and the constructor paired
        // the frame with its own function.
        unsafe { (self.run)(self.frame, self.part) }
    }
}

/// Run the part `part` of the frame of type `Frame` at `frame`.
///
/// # Specification
/// trivial.
///
/// # Safety
/// - requires: `frame` points at a live `Frame`.
unsafe fn run_frame<Frame>(
    frame: *const (),
    part: Part,
) where
    Frame: Runs,
{
    // SAFETY: `JobRef::of` made `frame` from a `&Frame`, and its party keeps
    // the frame alive until the part ends or comes back.
    let frame = unsafe { &*frame.cast::<Frame>() };
    frame.run(part);
}

/// A part that a party posted to a worker: the worker, and the seat's state
/// that the post wrote.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
pub struct Posted
{
    /// The worker that holds the part.
    worker: WorkerIndex,
    /// The seat's state that the post wrote.
    state: SeatState,
}

/// A seat's state: a count of the posts that it took, and what it holds.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SeatState(u64);

/// What a seat or a queue holds.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Holding
{
    /// Nothing: the worker is idle, or the queue is empty.
    Nothing,
    /// A part that no thread started.
    Posted,
    /// A part that the worker runs.
    Running,
}

impl SeatState
{
    /// The low bits that hold the seat's holding.
    const KIND: u64 = 0b11;

    /// What the seat holds.
    ///
    /// # Specification
    /// trivial.
    const fn holding(self) -> Holding
    {
        match self.0 & Self::KIND {
            1 => Holding::Posted,
            2 => Holding::Running,
            _ => Holding::Nothing,
        }
    }

    /// The same count of posts, holding `holding`.
    ///
    /// # Specification
    /// trivial.
    const fn holds(
        self,
        holding: Holding,
    ) -> Self
    {
        let kind = match holding {
            Holding::Nothing => 0,
            Holding::Posted => 1,
            Holding::Running => 2,
        };
        Self((self.0 & !Self::KIND) | kind)
    }

    /// The state of the seat's next post.
    ///
    /// # Specification
    /// trivial.
    const fn next_post(self) -> Self
    {
        Self((self.0 & !Self::KIND).wrapping_add(Self::KIND.wrapping_add(1))).holds(Holding::Posted)
    }
}

/// A worker's seat: the part that it holds, and the worker's park.
///
/// # Specification
/// trivial.
#[repr(align(128))]
struct Seat
{
    /// The count of posts, and what the seat holds.
    state: AtomicU64,
    /// The part, written while the seat holds nothing and read once it is
    /// running.
    job: UnsafeCell<MaybeUninit<JobRef>>,
    /// The worker's park.
    sleeper: Sleeper,
}

/// Only one party at a time reaches a seat's part.
///
/// # Safety
/// - unsafe invariants: the party that holds the worker's idle bit writes the
///   part while the seat holds nothing, and only then stores the post with
///   release. The worker reads the part only after its acquire exchange moves
///   the post to running.
// SAFETY: the party that holds the worker's idle bit writes the part while
// the seat holds nothing, then stores the post with release. The worker reads
// the part only after its acquire exchange moves the post to running, and the
// next write waits for the next idle bit.
unsafe impl Sync for Seat
{
}

impl Seat
{
    /// Take the posted part and run it, if the seat holds one.
    ///
    /// # Specification
    /// - ensures: [`Helped::Ran`] exactly when the call moved a post to
    ///   running, ran the part and left the seat holding nothing.
    /// - panics: none; a part that unwinds still leaves the seat holding
    ///   nothing.
    /// - executable: none — a party may post again as soon as the seat holds
    ///   nothing.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Workers`].
    /// - witness: `pool::tests::a_pool_visits_each_item_once_from_a_state_per_busy_worker`
    fn run_posted(&self) -> Helped
    {
        let state = SeatState(self.state.load(Ordering::Acquire));
        if state.holding() != Holding::Posted
            || self
                .state
                .compare_exchange(
                    state.0,
                    state.holds(Holding::Running).0,
                    Ordering::Acquire,
                    Ordering::Relaxed,
                )
                .is_err()
        {
            return Helped::Idle;
        }
        // SAFETY: the exchange moved this post to running, and the poster
        // wrote the part before it stored the post with release.
        let job = unsafe { self.job.get().read().assume_init() };
        // SAFETY: the poster keeps the frame alive until the part ends, since
        // its wait sees the part running and cannot take it back.
        let unwound = std::panic::catch_unwind(AssertUnwindSafe(|| unsafe { job.execute() }));
        drop(unwound);
        self.state
            .store(state.holds(Holding::Nothing).0, Ordering::Release);
        Helped::Ran
    }

    /// What the seat holds.
    ///
    /// # Specification
    /// trivial.
    fn holding(&self) -> Holding
    {
        SeatState(self.state.load(Ordering::Acquire)).holding()
    }
}

/// The workers' idle bits: one bit for each worker, set while it holds no
/// part.
///
/// # Specification
/// trivial.
#[repr(transparent)]
struct Idle(Box<[AtomicU64]>);

/// One bit of a word of idle bits.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Mask(u64);

/// Whether a party took a worker's idle bit.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Claimed
{
    /// The party holds the bit, so no other party posts to the worker.
    Took,
    /// Another party holds the bit.
    Taken,
}

impl Idle
{
    /// The bits of `count` workers, each set.
    ///
    /// # Specification
    /// trivial.
    fn full(count: NonZeroUsize) -> Self
    {
        let count = count.get();
        Self(
            (0 .. count.div_ceil(64))
                .map(|word| {
                    let below = count.saturating_sub(word.saturating_mul(64));
                    let mask = u32::try_from(below)
                        .ok()
                        .and_then(|shift| 1_u64.checked_shl(shift))
                        .map_or(u64::MAX, |bit| bit.wrapping_sub(1));
                    AtomicU64::new(mask)
                })
                .collect(),
        )
    }

    /// The bits of `count` workers, each clear.
    ///
    /// # Specification
    /// trivial.
    fn empty(count: NonZeroUsize) -> Self
    {
        Self(
            (0 .. count.get().div_ceil(64))
                .map(|_| AtomicU64::new(0))
                .collect(),
        )
    }

    /// Take the bit of an idle worker: the lowest of those whose bit
    /// `spinning` sets, else the lowest of all. A spinning worker takes its
    /// part with no wake.
    ///
    /// # Specification
    /// - ensures: a worker whose bit this call cleared, or absent when no bit
    ///   was set at the read of its word.
    /// - panics: none.
    /// - executable: none — another party may set or clear a bit at once.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Workers`].
    /// - witness: `pool::tests::a_pool_visits_each_item_once_from_a_state_per_busy_worker`
    fn claim_any(
        &self,
        spinning: &Idle,
    ) -> Maybe<WorkerIndex, unseated::Absent>
    {
        let awake = self.claim_within(|at| {
            spinning
                .0
                .get(at)
                .map_or(0, |word| word.load(Ordering::Relaxed))
        });
        match awake {
            Maybe::Present(worker) => Maybe::Present(worker),
            Maybe::Absent(_) => self.claim_within(|_| u64::MAX),
        }
    }

    /// Take the lowest set bit among those that `within` sets for each word.
    ///
    /// # Specification
    /// trivial.
    fn claim_within<Within>(
        &self,
        within: Within,
    ) -> Maybe<WorkerIndex, unseated::Absent>
    where
        Within: Fn(usize) -> u64,
    {
        for (at, word) in self.0.iter().enumerate() {
            let mut bits = word.load(Ordering::Relaxed);
            loop {
                let candidates = bits & within(at);
                if candidates == 0 {
                    break;
                }
                let bit = candidates.trailing_zeros();
                let mask = 1_u64.checked_shl(bit).unwrap_or_default();
                match word.compare_exchange_weak(
                    bits,
                    bits & !mask,
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => {
                        return Maybe::Present(WorkerIndex(
                            at.saturating_mul(64)
                                .saturating_add(usize::try_from(bit).unwrap_or_default()),
                        ));
                    },
                    Err(now) => bits = now,
                }
            }
        }
        Maybe::Absent(unseated::Absent::Busy)
    }

    /// Clear the bit of `worker`.
    ///
    /// # Specification
    /// trivial.
    fn clear(
        &self,
        worker: WorkerIndex,
    )
    {
        if let Some((bits, Mask(mask))) = self.word(worker) {
            bits.fetch_and(!mask, Ordering::Relaxed);
        }
    }

    /// Take the bit of `worker`.
    ///
    /// # Specification
    /// trivial.
    fn claim(
        &self,
        worker: WorkerIndex,
    ) -> Claimed
    {
        match self.word(worker) {
            Some((bits, Mask(mask))) if bits.fetch_and(!mask, Ordering::Acquire) & mask != 0 => {
                Claimed::Took
            },
            Some(_) | None => Claimed::Taken,
        }
    }

    /// Set the bit of `worker`.
    ///
    /// # Specification
    /// trivial.
    fn release(
        &self,
        worker: WorkerIndex,
    )
    {
        if let Some((bits, Mask(mask))) = self.word(worker) {
            bits.fetch_or(mask, Ordering::SeqCst);
        }
    }

    /// An idle worker, read after the caller's last write.
    ///
    /// # Specification
    /// trivial.
    fn any(&self) -> Maybe<WorkerIndex, unseated::Absent>
    {
        fence(Ordering::SeqCst);
        for (at, word) in self.0.iter().enumerate() {
            let bits = word.load(Ordering::Relaxed);
            if bits != 0 {
                return Maybe::Present(WorkerIndex(
                    at.saturating_mul(64)
                        .saturating_add(usize::try_from(bits.trailing_zeros()).unwrap_or_default()),
                ));
            }
        }
        Maybe::Absent(unseated::Absent::Busy)
    }

    /// The word and the mask of `worker`'s bit.
    ///
    /// # Specification
    /// trivial.
    fn word(
        &self,
        worker: WorkerIndex,
    ) -> Option<(&AtomicU64, Mask)>
    {
        let word = worker.0.checked_div(64)?;
        let bit = u32::try_from(worker.0.checked_rem(64)?).ok()?;
        Some((self.0.get(word)?, Mask(1_u64.checked_shl(bit)?)))
    }
}

/// A queue of jobs that wait for a worker, and its length for a read with no
/// lock.
///
/// # Specification
/// trivial.
struct Queue<Queued>
{
    /// The jobs, oldest first.
    jobs: Mutex<VecDeque<Queued>>,
    /// How many jobs wait.
    len: AtomicUsize,
}

impl<Queued> Queue<Queued>
{
    /// An empty queue.
    ///
    /// # Specification
    /// trivial.
    const fn new() -> Self
    {
        Self {
            jobs: Mutex::new(VecDeque::new()),
            len: AtomicUsize::new(0),
        }
    }

    /// The lock on the jobs. A poisoned lock still gives the jobs: no lock is
    /// held while a job runs.
    ///
    /// # Specification
    /// trivial.
    fn jobs(&self) -> MutexGuard<'_, VecDeque<Queued>>
    {
        match self.jobs.lock() {
            Ok(jobs) => jobs,
            Err(poisoned) => poisoned.into_inner(),
        }
    }

    /// Put `job` at the back.
    ///
    /// # Specification
    /// trivial.
    fn push(
        &self,
        job: Queued,
    )
    {
        self.jobs().push_back(job);
        self.len.fetch_add(1, Ordering::SeqCst);
    }

    /// Take the oldest job.
    ///
    /// # Specification
    /// trivial.
    fn pop(&self) -> Option<Queued>
    {
        if self.len.load(Ordering::SeqCst) == 0 {
            return None;
        }
        let job = self.jobs().pop_front()?;
        self.len.fetch_sub(1, Ordering::SeqCst);
        Some(job)
    }

    /// Whether a job waits.
    ///
    /// # Specification
    /// trivial.
    fn holding(&self) -> Holding
    {
        if self.len.load(Ordering::SeqCst) == 0 {
            Holding::Nothing
        }
        else {
            Holding::Posted
        }
    }
}

/// A standing job: work that outlives the fork that started it.
type Standing = Box<dyn FnOnce() + Send>;

/// What the workers and their parties share.
///
/// # Specification
/// trivial.
struct Shared
{
    /// One seat for each worker.
    seats: Box<[Seat]>,
    /// The idle bits.
    idle: Idle,
    /// The bits of the idle workers that spin, not yet parked: a hint for a
    /// post, never a claim.
    spinning: Idle,
    /// The spawns that found no idle worker.
    spawned: Queue<JobRef>,
    /// The standing jobs.
    standing: Queue<Standing>,
    /// Set once the pool is dropped: each worker ends once no job waits.
    ended: AtomicBool,
    /// The host's park-to-wake cost in nanoseconds: zero until the pool has
    /// measured or read it, so each worker parks at once meanwhile.
    park: AtomicU64,
}

impl Shared
{
    /// The host's park-to-wake cost.
    ///
    /// # Specification
    /// trivial.
    fn park(&self) -> Duration
    {
        Duration::from_nanos(self.park.load(Ordering::Relaxed))
    }

    /// Whether a queued job waits for a worker.
    ///
    /// # Specification
    /// trivial.
    fn queued(&self) -> Holding
    {
        match (self.spawned.holding(), self.standing.holding()) {
            (Holding::Nothing, Holding::Nothing) => Holding::Nothing,
            _ => Holding::Posted,
        }
    }
}

thread_local! {
    /// The address of the pool and the place of the worker that the current
    /// thread is.
    static CURRENT: Cell<Option<(usize, WorkerIndex)>> = const { Cell::new(None) };
}

/// The place of the current thread among the workers of the pool that runs
/// it, whichever pool that is.
///
/// # Specification
/// - ensures: present exactly when the current thread is a worker of a pool.
/// - panics: none.
/// - executable: none — the answer is a thread-local value.
///
/// # Adequacy
/// - hypothesis: L3 — a recorded fork marks each job on the ring of its thread.
/// - witness: `pool::recording::tests::a_recorded_fork_marks_each_item_with_its_declaration`
#[cfg(feature = "instrument")]
#[must_use]
pub fn current_worker() -> Maybe<WorkerIndex, unseated::Absent>
{
    match CURRENT.with(Cell::get) {
        Some((_, worker)) => Maybe::Present(worker),
        None => Maybe::Absent(unseated::Absent::Outside),
    }
}

/// The driver's worker threads, each parked on its own seat while it holds no
/// part.
///
/// # Specification
/// - provides: the post of a part to an idle worker and its take-back, the
///   queue of spawns and of standing jobs, and the fork of a frame's parts over
///   the workers and the calling thread.
/// - panics: none of its own.
/// - executable: none — the threads are the program's.
///
/// # Adequacy
/// - hypothesis: L3 — forks at two and four workers, nested forks, a schedule
///   whose jobs fork again, and spawns that wait for one another end with each
///   part run once.
/// - witness: `pool::tests::a_pool_visits_each_item_once_from_a_state_per_busy_worker`
/// - witness: `pool::tests::a_schedule_whose_jobs_fork_again_ends`
/// - witness: `pool::tests::nested_spawns_sum_the_leaves_at_every_width`
pub struct Workers
{
    /// What the workers share.
    shared: Arc<Shared>,
}

impl core::fmt::Debug for Workers
{
    /// Name the count of workers.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.debug_struct("Workers")
            .field("count", &self.shared.seats.len())
            .finish()
    }
}

impl Workers
{
    /// Start `threads` workers, each idle and parked on its seat.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one thread for each of `threads`, each idle.
    /// - fails: the host's error when it refuses a thread; the threads that
    ///   started end at once.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the host's error for the first thread that it refused.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Workers`].
    /// - witness: `pool::tests::a_pool_visits_each_item_once_from_a_state_per_busy_worker`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            pool_only_threads,
            reason = "pool: this is the workspace's one work pool, built once at the host's width"
        )
    )]
    pub fn start(
        threads: Threads,
        kept: Option<&Path>,
    ) -> Result<Self, std::io::Error>
    {
        let count = NonZeroUsize::from(threads);
        let mut parked = Vec::with_capacity(count.get());
        let mut senders = Vec::with_capacity(count.get());
        for at in 0 .. count.get() {
            let (sender, receiver) = std::sync::mpsc::channel::<Arc<Shared>>();
            let handle = std::thread::Builder::new()
                .name(alloc::format!("gandr-pool-{at}"))
                .spawn(move || {
                    if let Ok(shared) = receiver.recv() {
                        serve(&shared, WorkerIndex(at));
                    }
                })?;
            parked.push(handle.thread().clone());
            senders.push(sender);
        }
        let shared = Arc::new(Shared {
            seats: parked
                .into_iter()
                .map(|thread| Seat {
                    state: AtomicU64::new(0),
                    job: UnsafeCell::new(MaybeUninit::uninit()),
                    sleeper: Sleeper::of(thread),
                })
                .collect(),
            idle: Idle::full(count),
            spinning: Idle::empty(count),
            spawned: Queue::new(),
            standing: Queue::new(),
            ended: AtomicBool::new(false),
            park: AtomicU64::new(0),
        });
        for sender in senders {
            // A worker that cannot receive has ended, and no party posts to a
            // pool that never started.
            drop(sender.send(Arc::clone(&shared)));
        }
        let workers = Self { shared };
        let cost = workers.park_cost(threads, kept);
        workers.shared.park.store(
            u64::try_from(cost.as_nanos()).unwrap_or(u64::MAX),
            Ordering::Relaxed,
        );
        Ok(workers)
    }

    /// The host's park-to-wake cost at this width: the number kept in
    /// `kept`, or else a fresh measure, which is then kept there.
    ///
    /// # Specification
    /// - requires: no worker holds a part.
    /// - ensures: the number that `kept` holds for this width when it reads as
    ///   one; else a fresh measure, which the call then writes there by a
    ///   rename, so no reader sees half a number. A write that fails leaves the
    ///   measure in use and nothing kept.
    /// - panics: none.
    /// - executable: none — the answer is the host's timing.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a pool with a kept number starts with it, and one
    ///   with none keeps its measure.
    /// - witness: `pool::tests::a_pool_keeps_its_measured_park_and_reads_it_again`
    fn park_cost(
        &self,
        threads: Threads,
        kept: Option<&Path>,
    ) -> Duration
    {
        let file = kept.map(|directory| {
            directory.join(alloc::format!("park-{}", NonZeroUsize::from(threads).get()))
        });
        if let Some(cost) = file.as_deref().and_then(read_cost) {
            return cost;
        }
        let cost = self.measure();
        if let Some(file) = file.as_deref() {
            keep_cost(file, cost);
        }
        cost
    }

    /// Measure the host's park-to-wake cost: half the median of [`TRIPS`]
    /// round trips to a parked worker, each of which pays two wakes.
    ///
    /// # Specification
    /// - requires: no worker holds a part, and the cost in use is zero, so each
    ///   worker parks at once.
    /// - ensures: half the median round trip; zero when no trip ran.
    /// - panics: none.
    /// - executable: none — the answer is the host's timing.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Workers::park_cost`].
    /// - witness: `pool::tests::a_pool_keeps_its_measured_park_and_reads_it_again`
    fn measure(&self) -> Duration
    {
        let mut trips = [Duration::ZERO; TRIPS];
        for trip in &mut trips {
            // Let the worker of the last trip reach its park.
            std::thread::sleep(SETTLE);
            let frame = Trip {
                done: AtomicBool::new(false),
                waiter: std::thread::current(),
            };
            let started = Instant::now();
            // SAFETY: the loop below waits until the worker ran the part, so
            // the frame outlives the post.
            if let Maybe::Absent(_) = unsafe { self.post(JobRef::of(&frame, Part(0))) } {
                continue;
            }
            while !frame.done.load(Ordering::Acquire) {
                std::thread::park();
            }
            *trip = started.elapsed();
        }
        trips.sort_unstable();
        trips
            .get(TRIPS.checked_div(2).unwrap_or_default())
            .copied()
            .unwrap_or_default()
            .checked_div(2)
            .unwrap_or_default()
    }

    /// The park-to-wake cost that the workers use.
    ///
    /// # Specification
    /// trivial.
    pub fn park(&self) -> Duration
    {
        self.shared.park()
    }

    /// The place of the current thread among these workers.
    ///
    /// # Specification
    /// - ensures: present exactly when the current thread is one of these
    ///   workers.
    /// - panics: none.
    /// - executable: none — the answer is a thread-local value.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fork records where each item ran.
    /// - witness: `pool::tests::a_pool_forks_on_its_own_threads`
    #[must_use]
    pub fn current(&self) -> Maybe<WorkerIndex, unseated::Absent>
    {
        let pool = Arc::as_ptr(&self.shared).addr();
        match CURRENT.with(Cell::get) {
            Some((at, worker)) if at == pool => Maybe::Present(worker),
            Some(_) | None => Maybe::Absent(unseated::Absent::Outside),
        }
    }

    /// Post `job` to the lowest idle worker and wake it.
    ///
    /// # Specification
    /// - ensures: a post exactly when the call took an idle worker's bit; the
    ///   worker then holds the part, and runs it unless the poster takes it
    ///   back. Absent when every worker holds a part.
    /// - panics: none.
    /// - executable: none — the worker may start the part before the call
    ///   returns.
    ///
    /// # Safety
    /// - requires: the job's frame lives until [`Workers::retract`] answers
    ///   [`Retracted::Back`] for the post, or until the part ends.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Workers`].
    /// - witness: `pool::tests::a_pool_visits_each_item_once_from_a_state_per_busy_worker`
    pub unsafe fn post(
        &self,
        job: JobRef,
    ) -> Maybe<Posted, unseated::Absent>
    {
        let worker = match self.shared.idle.claim_any(&self.shared.spinning) {
            Maybe::Present(worker) => worker,
            Maybe::Absent(absent) => return Maybe::Absent(absent),
        };
        let Some(seat) = self.shared.seats.get(worker.0)
        else {
            return Maybe::Absent(unseated::Absent::Busy);
        };
        let state = SeatState(seat.state.load(Ordering::Relaxed)).next_post();
        // SAFETY: this party holds the worker's idle bit and the seat holds
        // nothing, so the worker reads no part until the store below.
        unsafe { seat.job.get().write(MaybeUninit::new(job)) };
        seat.state.store(state.0, Ordering::Release);
        seat.sleeper.wake();
        Maybe::Present(Posted { worker, state })
    }

    /// Take back the part of `posted`, unless its worker started it.
    ///
    /// # Specification
    /// - ensures: [`Retracted::Back`] exactly when the worker had not moved the
    ///   post to running; the seat then holds nothing, and the worker is idle
    ///   again.
    /// - panics: none.
    /// - executable: none — the worker's exchange races this one.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fork whose calling thread ends its share before a
    ///   worker wakes runs each item once.
    /// - witness: `pool::tests::a_pool_visits_each_item_once_from_a_state_per_busy_worker`
    pub fn retract(
        &self,
        posted: Posted,
    ) -> Retracted
    {
        let Some(seat) = self.shared.seats.get(posted.worker.0)
        else {
            return Retracted::Started;
        };
        match seat.state.compare_exchange(
            posted.state.0,
            posted.state.holds(Holding::Nothing).0,
            Ordering::AcqRel,
            Ordering::Relaxed,
        ) {
            Ok(_) => {
                self.shared.idle.release(posted.worker);
                Retracted::Back
            },
            Err(_) => Retracted::Started,
        }
    }

    /// Hand a spawned job to an idle worker, or else queue it.
    ///
    /// # Specification
    /// - ensures: the job is in a seat or in the queue of spawns. A queued job
    ///   wakes an idle worker, if any; a worker that ends a part reads the
    ///   queue before it parks.
    /// - panics: none.
    /// - executable: none — a worker may take the job before the call returns.
    ///
    /// # Safety
    /// - requires: the job's frame lives until its part ends.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Workers`].
    /// - witness: `pool::tests::nested_spawns_sum_the_leaves_at_every_width`
    pub unsafe fn spawn(
        &self,
        job: JobRef,
    )
    {
        // SAFETY: the caller keeps the frame until the part ends, and a spawn
        // is never taken back.
        if let Maybe::Present(_) = unsafe { self.post(job) } {
            return;
        }
        self.shared.spawned.push(job);
        self.rouse();
    }

    /// Queue `job` as standing work, which only a worker runs.
    ///
    /// # Specification
    /// - ensures: the job runs once on a worker, before the workers end.
    /// - panics: none.
    /// - executable: none — when a worker takes the job is the pool's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a submission on four threads runs beside the caller.
    /// - witness: `generation::tests::a_conflicting_submission_retires_the_older_generation`
    pub fn stand(
        &self,
        job: Standing,
    )
    {
        self.shared.standing.push(job);
        self.rouse();
    }

    /// Wake an idle worker, read after the caller's last write.
    ///
    /// # Specification
    /// trivial.
    fn rouse(&self)
    {
        if let Maybe::Present(worker) = self.shared.idle.any()
            && let Some(seat) = self.shared.seats.get(worker.0)
        {
            seat.sleeper.wake();
        }
    }

    /// Run one queued spawn on the calling thread.
    ///
    /// # Specification
    /// - ensures: [`Helped::Ran`] exactly when the call took a queued spawn and
    ///   ran it.
    /// - panics: none; a spawn keeps its own panic.
    /// - executable: none — a worker may take the spawn first.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Workers`].
    /// - witness: `pool::tests::a_wait_runs_its_job_here_or_helps_until_it_ends`
    pub fn help(&self) -> Helped
    {
        match self.shared.spawned.pop() {
            Some(job) => {
                // SAFETY: a spawn's frame lives until its part ends.
                unsafe { job.execute() };
                Helped::Ran
            },
            None => Helped::Idle,
        }
    }

    /// Run the parts of `frame`: `own` first on the calling thread, then each
    /// of the parts from `1` up to `parts` on an idle worker or on the calling
    /// thread.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `own` runs once with the count of parts posted to a worker.
    ///   Each part from `1` runs once on a worker, or else on the calling
    ///   thread: a part that found no idle worker, or that the calling thread
    ///   took back from its worker, runs after `own` when `back` is
    ///   [`Back::Run`], and never runs when `back` is [`Back::Drop`]. Once the
    ///   call returns, no worker runs a part of `frame`. A waiting thread polls
    ///   up to `spin` times, then parks until the last part wakes it. The fork
    ///   allocates nothing for 64 parts or fewer.
    /// - panics: the panic of `own`, or else the first panic of a part, once
    ///   every part ended or came back.
    /// - executable: none — where each part ran is the workers'.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — forks of one, three and 64 items on four workers, and
    ///   joins whose right half waits for the left one, run each part once and
    ///   resume each panic.
    /// - witness: `pool::tests::a_pool_visits_each_item_once_from_a_state_per_busy_worker`
    /// - witness: `pool::tests::a_right_half_may_wait_for_the_left_one`
    pub fn fork<Frame, Own, Out>(
        &self,
        frame: &Frame,
        parts: NonZeroUsize,
        (own, back): (Own, Back),
        spin: Spin,
    ) -> Out
    where
        Frame: Runs,
        Own: FnOnce(Posts) -> Out,
    {
        let parted = Parted {
            frame,
            left: AtomicUsize::new(0),
            waiter: std::thread::current(),
            panic: FirstPanic::default(),
        };
        let mut posts = Held::default();
        let mut next = 1_usize;
        while next < parts.get() {
            parted.left.fetch_add(1, Ordering::Relaxed);
            // SAFETY: this call waits below until each posted part ended or
            // came back, so `parted` outlives every post.
            match unsafe { self.post(JobRef::of(&parted, Part(next))) } {
                Maybe::Present(posted) => posts.push(posted),
                Maybe::Absent(_) => {
                    parted.left.fetch_sub(1, Ordering::Relaxed);
                    break;
                },
            }
            next = next.saturating_add(1);
        }
        let ran = std::panic::catch_unwind(AssertUnwindSafe(|| own(posts.count())));
        if back == Back::Run {
            for part in next .. parts.get() {
                parted.run_here(Part(part));
            }
        }
        for (at, held) in posts.iter().enumerate() {
            if self.retract(held) == Retracted::Back {
                parted.left.fetch_sub(1, Ordering::Relaxed);
                if back == Back::Run {
                    parted.run_here(Part(at.saturating_add(1)));
                }
            }
        }
        let mut polls = 0_u32;
        while parted.left.load(Ordering::Acquire) != 0 {
            if polls < spin.0 {
                polls = polls.saturating_add(1);
                core::hint::spin_loop();
            }
            else {
                std::thread::park();
            }
        }
        let out = ran.unwrap_or_else(|panic| std::panic::resume_unwind(panic));
        parted.panic.resume();
        out
    }
}

impl Drop for Workers
{
    /// End the workers: each ends once no job waits for it.
    ///
    /// # Specification
    /// - ensures: the end is set and every parked worker is woken.
    /// - panics: none.
    /// - executable: none — each worker reads the end on its own thread.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every test pool is dropped at its test's end.
    /// - witness: `pool::tests::a_pool_visits_each_item_once_from_a_state_per_busy_worker`
    fn drop(&mut self)
    {
        self.shared.ended.store(true, Ordering::SeqCst);
        for seat in &self.shared.seats {
            seat.sleeper.wake();
        }
    }
}

/// The most posts a fork holds in place before it allocates.
const IN_PLACE: usize = 64;

/// The posts of one fork: in place up to [`IN_PLACE`], then on the heap.
///
/// # Specification
/// trivial.
struct Held
{
    /// The first posts.
    near: [Option<Posted>; IN_PLACE],
    /// How many of `near` hold a post.
    count: usize,
    /// The posts past [`IN_PLACE`].
    far: Vec<Posted>,
}

impl Default for Held
{
    /// No post.
    ///
    /// # Specification
    /// trivial.
    fn default() -> Self
    {
        Self {
            near: [None; IN_PLACE],
            count: 0,
            far: Vec::new(),
        }
    }
}

impl Held
{
    /// Keep `posted`.
    ///
    /// # Specification
    /// trivial.
    fn push(
        &mut self,
        posted: Posted,
    )
    {
        match self.near.get_mut(self.count) {
            Some(slot) => {
                *slot = Some(posted);
                self.count = self.count.saturating_add(1);
            },
            None => self.far.push(posted),
        }
    }

    /// How many posts it holds.
    ///
    /// # Specification
    /// trivial.
    fn count(&self) -> Posts
    {
        Posts(self.count.saturating_add(self.far.len()))
    }

    /// The posts, in the order kept.
    ///
    /// # Specification
    /// trivial.
    fn iter(&self) -> impl Iterator<Item = Posted> + '_
    {
        self.near
            .iter()
            .take(self.count)
            .flatten()
            .copied()
            .chain(self.far.iter().copied())
    }
}

/// A fork's frame as its workers see it: the frame, the count of posted parts
/// not yet ended, the waiting thread and the first panic of a part.
///
/// # Specification
/// trivial.
struct Parted<'frame, Frame>
{
    /// The frame.
    frame: &'frame Frame,
    /// The posted parts that have not ended or come back.
    left: AtomicUsize,
    /// The thread that waits for the parts.
    waiter: Thread,
    /// The first panic of a part.
    panic: FirstPanic,
}

impl<Frame> Parted<'_, Frame>
where
    Frame: Runs,
{
    /// Run `part` on the calling thread, keeping its panic.
    ///
    /// # Specification
    /// trivial.
    fn run_here(
        &self,
        part: Part,
    )
    {
        if let Err(panic) = std::panic::catch_unwind(AssertUnwindSafe(|| self.frame.run(part))) {
            self.panic.keep(panic);
        }
    }
}

impl<Frame> Runs for Parted<'_, Frame>
where
    Frame: Runs,
{
    /// Run `part` on a worker, keep its panic, and count it down. The last
    /// part wakes the waiting thread.
    ///
    /// # Specification
    /// - ensures: the part ran, and the count fell by one. The call reads
    ///   nothing of the frame after the count falls, so the waiting thread may
    ///   drop the frame at once.
    /// - panics: none.
    /// - executable: none — the waiting thread reads the count.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Workers::fork`].
    /// - witness: `pool::tests::a_pool_visits_each_item_once_from_a_state_per_busy_worker`
    fn run(
        &self,
        part: Part,
    )
    {
        self.run_here(part);
        let waiter = self.waiter.clone();
        if self.left.fetch_sub(1, Ordering::AcqRel) == 1 {
            waiter.unpark();
        }
    }
}

/// The task of one worker: run each part posted to it, then each queued job,
/// and spin or park while there is none.
///
/// # Specification
/// - ensures: the worker runs each part posted to its seat once, and takes
///   queued jobs while it holds its own idle bit. With nothing to run, it spins
///   for at most the park-to-wake cost, then parks. It ends once the pool is
///   dropped and no job waits.
/// - panics: none; each part catches its own panic.
/// - executable: none — the task is the worker's whole life.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Workers`].
/// - witness: `pool::tests::a_pool_visits_each_item_once_from_a_state_per_busy_worker`
/// - witness: `generation::tests::a_conflicting_submission_retires_the_older_generation`
fn serve(
    shared: &Arc<Shared>,
    worker: WorkerIndex,
)
{
    CURRENT.with(|current| current.set(Some((Arc::as_ptr(shared).addr(), worker))));
    let Some(seat) = shared.seats.get(worker.0)
    else {
        return;
    };
    loop {
        if seat.run_posted() == Helped::Ran {
            shared.idle.release(worker);
            continue;
        }
        if shared.queued() == Holding::Posted {
            // Hold the worker's own bit while it runs a queued job, so no
            // party posts to it meanwhile; a lost bit means a post came.
            if shared.idle.claim(worker) == Claimed::Took {
                if let Some(job) = shared.spawned.pop() {
                    // SAFETY: a spawn's frame lives until its part ends.
                    let unwound =
                        std::panic::catch_unwind(AssertUnwindSafe(|| unsafe { job.execute() }));
                    drop(unwound);
                }
                else if let Some(job) = shared.standing.pop() {
                    drop(std::panic::catch_unwind(AssertUnwindSafe(job)));
                }
                shared.idle.release(worker);
            }
            continue;
        }
        if shared.ended.load(Ordering::SeqCst) {
            return;
        }
        let idle = Instant::now();
        let arrived = || {
            seat.holding() == Holding::Posted
                || shared.queued() == Holding::Posted
                || shared.ended.load(Ordering::Relaxed)
        };
        // A post within the park-to-wake cost costs no wake: spin up to the
        // cost, then park, so a longer gap costs at most twice a park at once.
        // Each round yields, so on a full host the core goes to a thread with
        // work.
        let park = shared.park();
        shared.spinning.release(worker);
        while !arrived() && idle.elapsed() < park {
            std::thread::yield_now();
        }
        shared.spinning.clear(worker);
        if !arrived() {
            seat.sleeper.sleep(arrived);
        }
    }
}

/// How many round trips the measure of a park and a wake takes.
const TRIPS: usize = 9;

/// The pause before each round trip of the measure, long enough for the
/// worker of the last trip to park.
const SETTLE: Duration = Duration::from_micros(200);

/// One round trip of the measure: the worker that runs it wakes the
/// measuring thread.
///
/// # Specification
/// trivial.
struct Trip
{
    /// Set once the worker ran the trip.
    done: AtomicBool,
    /// The measuring thread.
    waiter: Thread,
}

impl Runs for Trip
{
    /// Mark the trip done and wake the measuring thread. The call reads
    /// nothing of the trip after the mark, so the measuring thread may drop it
    /// at once.
    ///
    /// # Specification
    /// trivial.
    fn run(
        &self,
        _part: Part,
    )
    {
        let waiter = self.waiter.clone();
        self.done.store(true, Ordering::Release);
        waiter.unpark();
    }
}

/// The park-to-wake cost that the file at `file` keeps, in nanoseconds.
///
/// # Specification
/// trivial.
fn read_cost(file: &Path) -> Option<Duration>
{
    let kept = std::fs::read_to_string(file).ok()?;
    kept.trim().parse::<u64>().ok().map(Duration::from_nanos)
}

/// Keep `cost` in the file at `file`: write a sibling file, then rename it
/// over `file`, so a reader sees the old number or the new one whole.
///
/// # Specification
/// trivial.
fn keep_cost(
    file: &Path,
    cost: Duration,
)
{
    let partial = file.with_extension("partial");
    let nanos = u64::try_from(cost.as_nanos()).unwrap_or(u64::MAX);
    let kept = file
        .parent()
        .map_or(Ok(()), std::fs::create_dir_all)
        .and_then(|()| std::fs::write(&partial, alloc::format!("{nanos}\n")))
        .and_then(|()| std::fs::rename(&partial, file));
    // A host that refuses the write measures again at the next start.
    drop(kept);
}
