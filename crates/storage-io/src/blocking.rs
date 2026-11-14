//! The blocking form: one thread that the `Io` owns runs each order in turn
//! by positioned calls of the standard library, and answers through a
//! bounded channel, the completion queue of this form. A chain breaks as
//! the ring's does: an order that fails, or moves fewer bytes than it
//! asks, cancels each order linked after it.

use alloc::collections::VecDeque;
use alloc::sync::Arc;
use std::sync::Condvar;
use std::sync::Mutex;
use std::sync::MutexGuard;
use std::sync::PoisonError;
use std::sync::mpsc;
use std::thread::JoinHandle;

use crate::io::Chain;
use crate::io::Done;
use crate::io::Fate;
use crate::io::Operation;
use crate::io::Order;
use crate::ring::Count;
use crate::ring::Key;
use crate::ring::Moved;
use crate::sys::Errno;

/// Whether the thread takes more orders.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum State
{
    /// The thread waits for orders.
    Open,
    /// The thread runs what the queue holds, then ends.
    Closed,
}

/// The orders that the thread has not started, and the one it runs.
struct Queue
{
    /// The orders in turn.
    orders: VecDeque<Order>,
    /// The key of the order that the thread runs.
    running: Option<Key>,
    /// Whether the thread takes more orders.
    state: State,
}

/// The queue, shared between the `Io` and its thread.
struct Shared
{
    /// The queue.
    queue: Mutex<Queue>,
    /// Signalled when an order arrives or the queue closes.
    arrived: Condvar,
}

impl Shared
{
    /// The queue, locked. A panic of a holder leaves the queue whole, so a
    /// poisoned lock is taken as it stands.
    ///
    /// # Specification
    /// trivial.
    fn lock(&self) -> MutexGuard<'_, Queue>
    {
        self.queue.lock().unwrap_or_else(PoisonError::into_inner)
    }
}

/// Whether the order before broke its chain.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Link
{
    /// The next order runs.
    Whole,
    /// The next order completes cancelled.
    Broken,
}

/// The blocking form: the queue, the completion channel and the thread.
pub struct Blocking
{
    /// The queue, shared with the thread.
    shared: Arc<Shared>,
    /// The completions, at most `depth` waiting.
    done: mpsc::Receiver<Done>,
    /// The thread, joined at the drop.
    worker: Option<JoinHandle<()>>,
}

impl Blocking
{
    /// The blocking form of `depth` orders in flight, with its thread.
    ///
    /// # Specification
    /// - ensures: on `Ok`, a form whose thread waits for orders.
    /// - fails: the error number of a thread that does not spawn.
    /// - panics: none.
    /// - executable: none — the thread is the system's.
    ///
    /// # Errors
    /// The error number of a thread that does not spawn.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the blocking form completes a linked write, sync and
    ///   read in order.
    /// - witness: `tests::io::a_linked_write_sync_and_read_complete_in_order`
    #[inline]
    pub fn new(depth: Count) -> Result<Self, Errno>
    {
        let width = usize::try_from(u32::from(depth)).unwrap_or(usize::MAX);
        let shared = Arc::new(Shared {
            queue: Mutex::new(Queue {
                orders: VecDeque::with_capacity(width),
                running: None,
                state: State::Open,
            }),
            arrived: Condvar::new(),
        });
        let (sender, done) = mpsc::sync_channel(width);
        let theirs = Arc::clone(&shared);
        let worker = std::thread::Builder::new()
            .name(String::from("gandr-storage-io"))
            .spawn(move || serve(&theirs, &sender))
            .map_err(Errno::from)?;
        Ok(Self {
            shared,
            done,
            worker: Some(worker),
        })
    }

    /// Hand each staged order to the thread, in order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn flush(
        &self,
        staged: &mut Vec<Order>,
    )
    {
        self.shared.lock().orders.extend(staged.drain(..));
        self.shared.arrived.notify_one();
    }

    /// The next completion, parked until the thread gives one.
    ///
    /// # Specification
    /// - ensures: on `Ok`, the completion of the next order that the thread
    ///   ran.
    /// - fails: [`Errno::INPUT_OUTPUT`] when the thread has ended.
    /// - panics: none.
    /// - executable: none — the completion is the thread's.
    ///
    /// # Errors
    /// [`Errno::INPUT_OUTPUT`] when the thread has ended.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the blocking form's completions arrive in the order
    ///   of their submissions.
    /// - witness: `tests::io::a_linked_write_sync_and_read_complete_in_order`
    #[inline]
    pub fn wait(&self) -> Result<Done, Errno>
    {
        self.done.recv().map_err(|_ended| Errno::INPUT_OUTPUT)
    }

    /// The next completion that stands, if one does.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn take(&self) -> Option<Done>
    {
        self.done.try_recv().ok()
    }

    /// Cancel the order `target` if the thread has not started it.
    ///
    /// # Specification
    /// - ensures: `Ok` of 0 when the queue holds the target, which then
    ///   completes cancelled; [`Errno::ALREADY`] when the thread runs it;
    ///   [`Errno::NO_ENTRY`] when it has completed.
    /// - panics: none.
    /// - executable: none — the queue is shared with the thread.
    ///
    /// # Errors
    /// [`Errno::ALREADY`] or [`Errno::NO_ENTRY`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a cancel of a completed write finds no entry.
    /// - witness: `tests::io::a_cancel_after_completion_finds_no_entry`
    #[inline]
    pub fn cancel(
        &self,
        target: Key,
    ) -> Result<Moved, Errno>
    {
        let mut queue = self.shared.lock();
        if let Some(order) = queue.orders.iter_mut().find(|order| order.key == target) {
            order.fate = Fate::Cancelled;
            return Ok(Moved::from(0));
        }
        if queue.running == Some(target) {
            Err(Errno::ALREADY)
        }
        else {
            Err(Errno::NO_ENTRY)
        }
    }
}

impl Drop for Blocking
{
    /// Close the queue, let the thread run what it holds, and join it.
    ///
    /// # Specification
    /// trivial.
    fn drop(&mut self)
    {
        self.shared.lock().state = State::Closed;
        self.shared.arrived.notify_one();
        while self.done.recv().is_ok() {}
        if let Some(worker) = self.worker.take() {
            let _joined = worker.join();
        }
    }
}

/// The thread: run each order in turn, and send its completion.
///
/// # Specification
/// trivial.
fn serve(
    shared: &Shared,
    sender: &mpsc::SyncSender<Done>,
)
{
    let mut link = Link::Whole;
    while let Some(order) = next(shared) {
        let done = run(order, &mut link);
        shared.lock().running = None;
        if sender.send(done).is_err() {
            return;
        }
    }
}

/// The next order, parked until one arrives; `None` once the queue is
/// closed and empty.
///
/// # Specification
/// trivial.
fn next(shared: &Shared) -> Option<Order>
{
    let mut queue = shared.lock();
    loop {
        if let Some(order) = queue.orders.pop_front() {
            queue.running = Some(order.key);
            return Some(order);
        }
        if queue.state == State::Closed {
            return None;
        }
        queue = shared
            .arrived
            .wait(queue)
            .unwrap_or_else(PoisonError::into_inner);
    }
}

/// Run `order` by one positioned call, after the chain of the order before.
///
/// # Specification
/// - ensures: the order's completion. A cancelled order, or one after a broken
///   chain, completes with [`Errno::CANCELLED`] and runs nothing. A linked
///   order that fails or moves fewer bytes than it asks breaks the chain.
/// - panics: none.
/// - executable: none — the file is the kernel's.
///
/// # Adequacy
/// - hypothesis: L3 — a write that fails cancels the sync linked to it, as the
///   ring does.
/// - witness: `tests::io::a_failed_write_cancels_its_linked_sync`
fn run(
    mut order: Order,
    link: &mut Link,
) -> Done
{
    let outcome = if *link == Link::Broken || order.fate == Fate::Cancelled {
        Err(Errno::CANCELLED)
    }
    else {
        match order.operation {
            Operation::Read {
                ref handle,
                ref mut buffer,
            } => buffer.read_from(handle.file(), order.at),
            Operation::Write {
                ref handle,
                ref buffer,
            } => buffer.write_into(handle.file(), order.at),
            Operation::Sync { ref handle } => handle
                .file()
                .sync_all()
                .map(|()| Moved::from(0))
                .map_err(Errno::from),
            Operation::Cancel { .. } => Err(Errno::INVALID),
        }
    };
    let whole = outcome.is_ok_and(|moved| moved >= order.operation.asked());
    *link = if order.chain == Chain::Linked && !whole {
        Link::Broken
    }
    else {
        Link::Whole
    };
    order.done(outcome)
}
