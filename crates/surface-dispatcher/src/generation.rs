//! Work keyed by what it is valid under: a newer submission for the same slot
//! retires the older generation, and a retired result is never delivered.
//!
//! # A slot, a key and a generation
//!
//! [`Generations`] runs jobs on the driver's [`Pool`]. Each submission names
//! its *slot*, what the job is about (one stage's work on one item, say), and
//! its *key*, what the job's result is valid under (that stage's key for the
//! item: its text for the parse, its canonical content for the checker). A
//! slot has one current generation:
//!
//! - a submission under the slot's current key starts nothing, because the
//!   running or delivered job already answers it;
//! - a submission under another key retires the current generation and starts a
//!   new one;
//! - other slots' generations are untouched, so a job for an item a change did
//!   not reach runs on and is delivered.
//!
//! A change re-keys exactly the slots whose stage key it moved. A whitespace
//! edit moves the parse's key and not the checker's, so it retires the parse
//! of the touched form and nothing else (#1547).
//!
//! # Stopping is an economy; dropping is the guarantee
//!
//! A job is handed a [`Watch`] and polls it at its step boundaries. Once its
//! generation is retired, [`Watch::poll`] answers [`Retired`], and the job
//! returns it and ends early. A job that never polls runs to its end. Either
//! way, delivery compares the result's generation with its slot's current one
//! and drops the result when they differ. A retired result is never delivered,
//! whether or not its job stopped.
//!
//! At one thread, or when the host refused the pool's threads, a job runs on
//! the calling thread inside [`Generations::submit`], and delivery drops a
//! retired result exactly as it does one from a worker. A job's panic is caught
//! on the thread that ran it and resumed where its result is delivered.
//!
//! **A flag per generation, compared again at delivery.** A submission makes
//! its generation a flag, which retirement sets and the job's [`Watch`] reads
//! with one load. Delivery compares generation numbers on the thread that owns
//! the slots, so the flag decides only when a job stops, never what is
//! delivered. The alternatives were these:
//!
//! - _A counter per slot that each job reads against its own generation._ It
//!   answers the same question with a second load and keeps the slot's counter
//!   alive in every job. Reversal: a job that needs to know how many
//!   generations passed it.
//! - _Retirement checked at delivery alone._ It is as correct, but the pool
//!   spends its threads on results nobody reads. Reversal: a job with no step
//!   boundary to poll at.
//! - _An asynchronous runtime's cancellation token, such as `tokio-util`'s
//!   `CancellationToken`._ It cancels futures; the engine's jobs are
//!   synchronous steps on `rayon` threads, which would take on a runtime for
//!   one flag. Reversal: the engine's jobs become futures.
//!
//! The results come back on one `std::sync::mpsc` channel that the owner of
//! the slots drains, so the slots are never shared across threads. The choice
//! reverses on a measured contention on that channel.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use core::any::Any;
use core::fmt;
use core::panic::AssertUnwindSafe;
use core::sync::atomic::AtomicBool;
use core::sync::atomic::Ordering;
use std::sync::mpsc;

use anodized::spec;
use gandr_core_checker::Demand;
use gandr_core_checker::Retirement;
use quenchant_shape::shape::Maybe;

use crate::pool::Pool;

quenchant_shape::reason_enum! {
    /// Why no result is delivered.
    pub mod delivery {
        /// The reason no result is delivered.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No job is running: every result was delivered or dropped.
            Idle,
            /// A job is running, and none has finished that can be delivered.
            Pending,
        }
    }
}

/// A job's generation was retired by a newer submission for its slot.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Retired;

impl fmt::Display for Retired
{
    /// Name the retirement.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str("retired by a newer submission for its slot")
    }
}

impl core::error::Error for Retired
{
}

/// What a running job polls at its step boundaries.
///
/// # Specification
/// - provides: the retirement of the one generation the job runs under.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a job polling in a loop stops once a submission under
///   another key follows it.
/// - witness: `generation::tests::a_conflicting_submission_retires_the_older_generation`
#[derive(Clone, Debug)]
#[repr(transparent)]
pub struct Watch(Arc<AtomicBool>);

impl Watch
{
    /// Whether the job's generation still stands.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Retired`] exactly once a submission for the job's slot
    ///   under another key has followed the job's own; it stays retired.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`Retired`] once the job's generation is retired.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Watch`].
    /// - witness: `generation::tests::a_conflicting_submission_retires_the_older_generation`
    #[inline]
    #[spec(ensures: |ret| ret.is_ok() || self.0.load(Ordering::Acquire))]
    pub fn poll(&self) -> Result<(), Retired>
    {
        if self.0.load(Ordering::Acquire) {
            Err(Retired)
        }
        else {
            Ok(())
        }
    }
}

impl Retirement for Watch
{
    type Retired = Retired;

    /// Wanted while the job's generation stands, then [`Retired`].
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: answers as [`Watch::poll`]: retired exactly once a submission
    ///   for the job's slot under another key has followed the job's own.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an admission run under a watch stops at its next
    ///   declaration once its generation is retired.
    /// - witness: `generation::tests::a_retired_slot_delivers_nothing`
    #[inline]
    #[spec(ensures: |ret| matches!(ret, Demand::Wanted) == self.poll().is_ok())]
    fn demand(&self) -> Demand<Retired>
    {
        match self.poll() {
            Ok(()) => Demand::Wanted,
            Err(retired) => Demand::Retired(retired),
        }
    }
}

/// What a submission did.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Submitted
{
    /// A new generation started and retired the slot's previous one, if any.
    Started,
    /// The slot's current generation is under the same key, so nothing
    /// started.
    Held,
}

/// A job's result, delivered because its generation is still its slot's
/// current one.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Delivered<Slot, Key, Output>
{
    /// What the job was about.
    pub slot: Slot,
    /// What its result is valid under.
    pub key: Key,
    /// The result.
    pub output: Output,
}

/// How a job ended.
enum Ended<Output>
{
    /// It returned its result.
    Finished(Output),
    /// It saw its retirement and stopped.
    Stopped,
    /// It panicked, with this payload.
    Panicked(Box<dyn Any + Send>),
}

/// One ended job, as sent back to the owner of the slots.
struct Done<Slot, Output>
{
    /// The job's slot.
    slot: Slot,
    /// The generation it ran under.
    generation: Generation,
    /// How it ended.
    ended: Ended<Output>,
}

/// One submission's place in the order of every submission.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
struct Generation(u64);

/// A slot's current generation.
#[derive(Debug)]
struct Current<Key>
{
    /// What its result is valid under.
    key: Key,
    /// Which submission it is.
    generation: Generation,
    /// Set when a newer submission retires it.
    retired: Arc<AtomicBool>,
}

/// Jobs on the driver's pool, each keyed by what its result is valid under,
/// with one current generation per slot.
///
/// # Specification
/// - provides: submission, which retires the slot's older generation when the
///   key differs, and delivery, which hands back only results whose generation
///   is still current.
/// - panics: a job's panic resumes at its delivery.
/// - executable: none — the jobs run on the pool's threads.
///
/// # Adequacy
/// - hypothesis: L3 — of two generations of one slot, only the newer one's
///   result is delivered, whether the older job stopped or ran to its end, and
///   another slot's result is delivered beside it, at four threads and at one.
/// - witness: `generation::tests::a_conflicting_submission_retires_the_older_generation`
/// - witness: `generation::tests::a_retired_result_is_dropped_though_its_job_finished`
/// - witness: `generation::tests::a_serial_pool_runs_each_job_on_the_caller`
#[derive(Debug)]
pub struct Generations<'pool, Slot, Key, Output>
{
    /// The threads the jobs run on.
    pool: &'pool Pool,
    /// Each slot's current generation.
    current: BTreeMap<Slot, Current<Key>>,
    /// The next submission's generation.
    next: Generation,
    /// How many started jobs have not yet been received.
    running: usize,
    /// What each job sends its end on.
    sender: mpsc::Sender<Done<Slot, Output>>,
    /// Where the ends arrive.
    receiver: mpsc::Receiver<Done<Slot, Output>>,
    /// What each job's end wakes, once it is sent.
    wake: Wake,
}

/// What a job's end wakes once it is sent: the owner's loop, when it sleeps
/// until something arrives.
#[derive(Clone)]
#[repr(transparent)]
struct Wake(Option<Arc<dyn Fn() + Send + Sync>>);

impl fmt::Debug for Wake
{
    /// Writes whether a wake is set.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.debug_tuple("Wake").field(&self.0.is_some()).finish()
    }
}

impl<'pool, Slot, Key, Output> Generations<'pool, Slot, Key, Output>
where
    Slot: Ord + Clone + Send + 'static,
    Key: Eq + Clone,
    Output: Send + 'static,
{
    /// No slot, no job, on `pool`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(pool: &'pool Pool) -> Self
    {
        let (sender, receiver) = mpsc::channel();
        Self {
            pool,
            current: BTreeMap::new(),
            next: Generation(0),
            running: 0,
            sender,
            receiver,
            wake: Wake(None),
        }
    }

    /// No slot, no job, on `pool`, each job's end waking `wake` once it can
    /// be received.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Generations::new`], holding `wake`; every job submitted
    ///   later calls `wake` once after its end is sent, so a
    ///   [`Generations::ready`] the wake prompts receives it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an owner that sleeps until woken receives every
    ///   delivery it is woken for.
    /// - witness: `generation::tests::a_woken_owner_finds_the_end_ready`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.current.is_empty() && ret.running == 0 && ret.wake.0.is_some())]
    pub fn waking(
        pool: &'pool Pool,
        wake: Arc<dyn Fn() + Send + Sync>,
    ) -> Self
    {
        Self {
            wake: Wake(Some(wake)),
            ..Self::new(pool)
        }
    }

    /// Run `job` for `slot` under `key`, unless the slot's current generation
    /// is already under `key`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Submitted::Held`] when the slot's current key equals `key`,
    ///   and nothing runs; otherwise [`Submitted::Started`], the slot's
    ///   previous generation is retired, its [`Watch`] answers [`Retired`] from
    ///   now on, and `job` runs under the new one. On a pool of one thread, or
    ///   one the host refused, `job` has run on the calling thread when this
    ///   returns.
    /// - panics: none; a panic of `job` resumes at its delivery.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a resubmission under the current key runs nothing;
    ///   one under another key retires the running job.
    /// - witness: `generation::tests::a_submission_under_the_current_key_is_held`
    /// - witness: `generation::tests::a_conflicting_submission_retires_the_older_generation`
    #[inline]
    #[spec(
        captures: [held = self.current.get(&slot).is_some_and(|current| current.key == key)],
        ensures: |ret| matches!(ret, Submitted::Held) == held,
    )]
    pub fn submit<Job>(
        &mut self,
        slot: Slot,
        key: Key,
        job: Job,
    ) -> Submitted
    where
        Job: FnOnce(&Watch) -> Result<Output, Retired> + Send + 'static,
    {
        if self
            .current
            .get(&slot)
            .is_some_and(|current| current.key == key)
        {
            return Submitted::Held;
        }
        let generation = self.next;
        self.next = Generation(generation.0.saturating_add(1));
        let retired = Arc::new(AtomicBool::new(false));
        let watch = Watch(Arc::clone(&retired));
        let previous = self.current.insert(slot.clone(), Current {
            key,
            generation,
            retired,
        });
        if let Some(previous) = previous {
            previous.retired.store(true, Ordering::Release);
        }
        let sender = self.sender.clone();
        let wake = self.wake.clone();
        let run = move || {
            let ended = std::panic::catch_unwind(AssertUnwindSafe(|| job(&watch)))
                .map_or_else(Ended::Panicked, |ran| {
                    ran.map_or(Ended::Stopped, Ended::Finished)
                });
            // The receiver lives as long as the generations do: a send fails
            // only once they are dropped, when nothing would read the end.
            drop(sender.send(Done {
                slot,
                generation,
                ended,
            }));
            if let Wake(Some(ref wake)) = wake {
                wake();
            }
        };
        self.running = self.running.saturating_add(1);
        match self.pool.standing() {
            Maybe::Present(threads) => threads.spawn(run),
            Maybe::Absent(_) => run(),
        }
        Submitted::Started
    }

    /// Retire `slot`'s current generation, submitting nothing in its place.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the slot has no current generation; its last job's [`Watch`]
    ///   answers [`Retired`] from now on, and its result is never delivered. A
    ///   slot with no generation is left as it is.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a retired slot's running job stops and delivers
    ///   nothing, beside another slot's delivery.
    /// - witness: `generation::tests::a_retired_slot_delivers_nothing`
    #[inline]
    #[spec(ensures: !self.current.contains_key(slot))]
    pub fn retire(
        &mut self,
        slot: &Slot,
    )
    {
        if let Some(current) = self.current.remove(slot) {
            current.retired.store(true, Ordering::Release);
        }
    }

    /// The next result whose generation is still current, waiting for the
    /// running jobs.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each ended job is received once; a result is returned exactly
    ///   when its generation is its slot's current one, under that generation's
    ///   key; a retired job's result and a stopped job's end are dropped.
    ///   [`delivery::Absent::Idle`] once no started job is left.
    /// - panics: resumes the panic of a job it receives.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Generations`].
    /// - witness: `generation::tests::a_retired_result_is_dropped_though_its_job_finished`
    /// - witness: `generation::tests::a_panicking_job_resumes_at_its_delivery`
    #[inline]
    #[spec(ensures: |ret| matches!(ret, Maybe::Present(_)) || (self.running == 0 && matches!(ret, Maybe::Absent(delivery::Absent::Idle))))]
    pub fn wait(&mut self) -> Maybe<Delivered<Slot, Key, Output>, delivery::Absent>
    {
        while self.running > 0 {
            // The generations hold a sender, so the channel never disconnects.
            let Ok(done) = self.receiver.recv()
            else {
                break;
            };
            self.running = self.running.saturating_sub(1);
            if let Some(delivered) = self.settle(done) {
                return Maybe::Present(delivered);
            }
        }
        Maybe::Absent(delivery::Absent::Idle)
    }

    /// The next result whose generation is still current, among the jobs
    /// that have already ended.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Generations::wait`], without waiting:
    ///   [`delivery::Absent::Pending`] when a started job is still running and
    ///   none has ended that can be delivered.
    /// - panics: resumes the panic of a job it receives.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a running job is pending; a job run on the caller is
    ///   ready at once.
    /// - witness: `generation::tests::a_retired_result_is_dropped_though_its_job_finished`
    /// - witness: `generation::tests::a_serial_pool_runs_each_job_on_the_caller`
    #[inline]
    #[spec(ensures: |ret| match ret {
        Maybe::Present(_) => true,
        Maybe::Absent(delivery::Absent::Idle) => self.running == 0,
        Maybe::Absent(delivery::Absent::Pending) => self.running > 0,
    })]
    pub fn ready(&mut self) -> Maybe<Delivered<Slot, Key, Output>, delivery::Absent>
    {
        while self.running > 0 {
            let Ok(done) = self.receiver.try_recv()
            else {
                return Maybe::Absent(delivery::Absent::Pending);
            };
            self.running = self.running.saturating_sub(1);
            if let Some(delivered) = self.settle(done) {
                return Maybe::Present(delivered);
            }
        }
        Maybe::Absent(delivery::Absent::Idle)
    }

    /// `done` as a delivery, if its generation is its slot's current one and
    /// it finished.
    ///
    /// # Specification
    /// - ensures: a result under the slot's current key exactly when `done`'s
    ///   generation is current and its job finished.
    /// - panics: resumes the panic `done` carries, current or not.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Generations::wait`].
    /// - witness: `generation::tests::a_retired_result_is_dropped_though_its_job_finished`
    #[spec(ensures: |ret| ret.as_ref().is_none_or(|delivered| self.current.get(&delivered.slot).is_some_and(|current| current.key == delivered.key)))]
    fn settle(
        &self,
        done: Done<Slot, Output>,
    ) -> Option<Delivered<Slot, Key, Output>>
    {
        let Done {
            slot,
            generation,
            ended,
        } = done;
        let output = match ended {
            Ended::Finished(output) => output,
            Ended::Stopped => return None,
            Ended::Panicked(payload) => std::panic::resume_unwind(payload),
        };
        let key = self
            .current
            .get(&slot)
            .filter(|current| current.generation == generation)?
            .key
            .clone();
        Some(Delivered { slot, key, output })
    }
}

#[cfg(test)]
mod tests
{
    use alloc::sync::Arc;
    use core::num::NonZeroUsize;
    use core::sync::atomic::AtomicUsize;
    use core::sync::atomic::Ordering;
    use std::sync::mpsc;

    use gandr_core_checker::Demand;
    use gandr_core_checker::Retirement;
    use quenchant_shape::shape::Maybe;

    use super::Delivered;
    use super::Generations;
    use super::Submitted;
    use super::delivery;
    use crate::pool::Pool;
    use crate::width::Threads;
    use crate::width::Width;

    /// A pool of four threads.
    ///
    /// # Specification
    /// trivial.
    fn four() -> Pool
    {
        Pool::new(Width::Threads(Threads::from(
            NonZeroUsize::new(4_usize).unwrap(),
        )))
    }

    /// The delivery `answer` holds, if any.
    ///
    /// # Specification
    /// trivial.
    fn delivered<Answer>(answer: Maybe<Answer, delivery::Absent>) -> Answer
    {
        match answer {
            Maybe::Present(delivered) => delivered,
            Maybe::Absent(absent) => panic!("no delivery: {absent:?}"),
        }
    }

    #[test]
    fn a_conflicting_submission_retires_the_older_generation()
    {
        let pool = four();
        let mut generations: Generations<'_, &'static str, u32, u32> = Generations::new(&pool);
        let (started, began) = mpsc::channel();
        let (stopped, ended) = mpsc::channel();
        let first = generations.submit("a", 1, move |watch| {
            started.send(()).unwrap();
            loop {
                if let Err(retired) = watch.poll() {
                    stopped.send(()).unwrap();
                    return Err(retired);
                }
                std::thread::yield_now();
            }
        });
        assert_eq!(first, Submitted::Started);
        began.recv().unwrap();
        assert_eq!(generations.submit("b", 1, |_| Ok(10)), Submitted::Started);
        assert_eq!(generations.submit("a", 2, |_| Ok(20)), Submitted::Started);
        ended.recv().unwrap();
        let mut answers = [delivered(generations.wait()), delivered(generations.wait())];
        answers.sort_by_key(|answer| answer.slot);
        assert_eq!(answers, [
            Delivered {
                slot: "a",
                key: 2,
                output: 20,
            },
            Delivered {
                slot: "b",
                key: 1,
                output: 10,
            },
        ]);
        assert!(
            matches!(generations.wait(), Maybe::Absent(delivery::Absent::Idle)),
            "the stopped job delivers nothing"
        );
    }

    #[test]
    fn a_retired_result_is_dropped_though_its_job_finished()
    {
        let pool = four();
        let mut generations: Generations<'_, &'static str, u32, u32> = Generations::new(&pool);
        let (open, gate) = mpsc::channel::<()>();
        generations.submit("a", 1, move |_| {
            gate.recv().unwrap();
            Ok(10)
        });
        assert!(
            matches!(
                generations.ready(),
                Maybe::Absent(delivery::Absent::Pending)
            ),
            "a held job is pending"
        );
        generations.submit("a", 2, |_| Ok(20));
        open.send(()).unwrap();
        assert_eq!(delivered(generations.wait()), Delivered {
            slot: "a",
            key: 2,
            output: 20,
        });
        assert!(
            matches!(generations.wait(), Maybe::Absent(delivery::Absent::Idle)),
            "the job that never polled ran to its end, and its result was dropped"
        );
    }

    #[test]
    fn a_submission_under_the_current_key_is_held()
    {
        let pool = four();
        let mut generations: Generations<'_, &'static str, u32, u32> = Generations::new(&pool);
        let runs = Arc::new(AtomicUsize::new(0));
        let job = |runs: &Arc<AtomicUsize>| {
            let runs = Arc::clone(runs);
            move |_: &super::Watch| {
                runs.fetch_add(1, Ordering::Relaxed);
                Ok(10)
            }
        };
        assert_eq!(generations.submit("a", 1, job(&runs)), Submitted::Started);
        assert_eq!(generations.submit("a", 1, job(&runs)), Submitted::Held);
        assert_eq!(delivered(generations.wait()).key, 1);
        assert_eq!(
            generations.submit("a", 1, job(&runs)),
            Submitted::Held,
            "a delivered generation still answers its key"
        );
        assert!(matches!(
            generations.wait(),
            Maybe::Absent(delivery::Absent::Idle)
        ));
        assert_eq!(runs.load(Ordering::Relaxed), 1, "the job ran once");
        assert_eq!(generations.submit("a", 2, job(&runs)), Submitted::Started);
        assert_eq!(delivered(generations.wait()).key, 2);
    }

    #[test]
    fn a_serial_pool_runs_each_job_on_the_caller()
    {
        let pool = Pool::new(Width::SERIAL);
        let mut generations: Generations<'_, &'static str, u32, u32> = Generations::new(&pool);
        let caller = std::thread::current().id();
        generations.submit("a", 1, move |_| {
            assert_eq!(std::thread::current().id(), caller);
            Ok(10)
        });
        generations.submit("a", 2, move |_| {
            assert_eq!(std::thread::current().id(), caller);
            Ok(20)
        });
        assert_eq!(
            delivered(generations.ready()),
            Delivered {
                slot: "a",
                key: 2,
                output: 20,
            },
            "the job ran on the caller, so its result is ready at once"
        );
        assert!(matches!(
            generations.ready(),
            Maybe::Absent(delivery::Absent::Idle)
        ));
    }

    #[test]
    #[should_panic(expected = "the job's own panic")]
    fn a_panicking_job_resumes_at_its_delivery()
    {
        let pool = four();
        let mut generations: Generations<'_, &'static str, u32, u32> = Generations::new(&pool);
        generations.submit("a", 1, |_| panic!("the job's own panic"));
        let answer = generations.wait();
        panic!("delivery answered {answer:?} past the job's panic");
    }

    /// #1547: an owner that sleeps until a job's wake finds the job's end
    /// ready, so a loop woken by an admission never misses its delivery.
    #[test]
    fn a_woken_owner_finds_the_end_ready()
    {
        let pool = four();
        let (woke, woken) = mpsc::channel();
        let mut generations: Generations<'_, u32, u32, u32> = Generations::waking(
            &pool,
            Arc::new(move || {
                let _sent = woke.send(());
            }),
        );
        for job in 0_u32 .. 64_u32 {
            let _started = generations.submit(job, job, move |_| Ok(job));
            woken.recv().unwrap();
            assert_eq!(
                delivered(generations.ready()),
                Delivered {
                    slot: job,
                    key: job,
                    output: job,
                },
                "the woken owner receives the end at once"
            );
        }
    }

    /// #1547: a slot retired with nothing in its place stops its running job
    /// and delivers nothing, while another slot's result is delivered.
    #[test]
    fn a_retired_slot_delivers_nothing()
    {
        let pool = four();
        let mut generations: Generations<'_, &'static str, u32, u32> = Generations::new(&pool);
        let (started, began) = mpsc::channel();
        let _first = generations.submit("a", 1, move |watch| {
            started.send(()).unwrap();
            loop {
                if let Demand::Retired(retired) = Retirement::demand(watch) {
                    return Err(retired);
                }
                std::thread::yield_now();
            }
        });
        began.recv().unwrap();
        let _second = generations.submit("b", 1, |_| Ok(2));
        generations.retire(&"a");
        assert_eq!(delivered(generations.wait()), Delivered {
            slot: "b",
            key: 1,
            output: 2,
        });
        assert!(
            matches!(generations.wait(), Maybe::Absent(delivery::Absent::Idle)),
            "the retired slot's job stopped and delivered nothing"
        );
    }
}
