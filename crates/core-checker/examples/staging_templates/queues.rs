//! Observer transports: padded upstream rings, equal capacities, no kernel
//! dependency.

use alloc::sync::Arc;
use std::thread;

use ringbuf::traits::Consumer as _;
use ringbuf::traits::Producer as _;
use ringbuf::traits::Split as _;

use super::Natural;
use super::Threads;
use super::handoff::Command;
use super::handoff::Mode;
use super::handoff::Receipt;
use super::handoff::Scratch;
use super::handoff::Workload;
use super::handoff::execute;
use super::io;

/// More than every member in the 25-batch mixed stream.
const CAPACITY: usize = 0x4000;

/// Polling policy for both endpoints of each ring.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Wake
{
    /// Occupy execution capacity continuously, without sleeping.
    Busy,
    /// Spin 64 misses, then park until publication supplies a wake token.
    Park,
}

impl Wake
{
    /// Wait without losing a notification delivered before parking.
    ///
    /// # Specification
    /// - ensures: busy never parks; shared mode parks after 64 unsuccessful
    ///   polls.
    /// - panics: none.
    fn idle(
        self,
        misses: &mut Natural,
    )
    {
        if self == Self::Park && misses.0 >= 64 {
            thread::park();
            misses.0 = 0;
        }
        else {
            core::hint::spin_loop();
            misses.0 = misses.0.saturating_add(1);
        }
    }

    /// Supply a persistent wake token under the shared-machine policy.
    ///
    /// # Specification
    /// trivial.
    fn notify(
        self,
        target: &thread::Thread,
    )
    {
        if self == Self::Park {
            target.unpark();
        }
    }
}

/// Stable observer protocol label, without runtime string allocation.
#[repr(transparent)]
pub(super) struct Label(
    /// Static spelling used by selection and CSV output.
    pub &'static str,
);

impl core::fmt::Display for Label
{
    /// Render the borrowed report spelling.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(self.0)
    }
}

/// Standing worker topology.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Kind
{
    /// Native blocking MPMC jobs and results.
    Channel,
    /// Wait-free per-worker job and result rings.
    Rtrb(Wake),
    /// Lock-free per-worker job and result rings.
    Ringbuf(Wake),
    /// Injector, local FIFO deques, peer stealing, MPMC results.
    Steal,
}

impl Kind
{
    /// Stable measurement label.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn label(self) -> Label
    {
        Label(match self {
            | Self::Channel => "channel",
            | Self::Rtrb(Wake::Busy) => "rtrb-busy",
            | Self::Rtrb(Wake::Park) => "rtrb-park",
            | Self::Ringbuf(Wake::Busy) => "ringbuf-busy",
            | Self::Ringbuf(Wake::Park) => "ringbuf-park",
            | Self::Steal => "steal",
        })
    }
}

/// Publication policy, orthogonal to task grain and consumer drain size.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Publication
{
    /// One push or pop per descriptor.
    Each,
    /// Whole-wave `push_slice`/chunks; `pop_slice`/chunks up to the drain
    /// limit.
    Batch,
}

impl Publication
{
    /// Stable measurement label.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn label(self) -> Label
    {
        Label(match self {
            | Self::Each => "each",
            | Self::Batch => "batch",
        })
    }
}

/// Complete transport parameters for one matrix row.
#[derive(Clone, Copy)]
pub(super) struct Wire
{
    /// Queue topology and wake policy.
    pub kind: Kind,
    /// Per-message or chunked publication.
    pub publication: Publication,
    /// Maximum messages consumed per worker turn, either one or 32.
    pub drain: Natural,
}

/// Parent or worker producer endpoint.
enum Send<T>
{
    /// Bounded native channel.
    Channel(crossbeam_channel::Sender<T>),
    /// Wait-free ring.
    Rtrb(rtrb::Producer<T>),
    /// Cached lock-free ring.
    Ringbuf(ringbuf::HeapProd<T>),
}

impl<T> Send<T>
where
    T: Copy,
{
    /// Publish the complete slice, preserving order and every full-queue item.
    ///
    /// # Specification
    /// - requires: at most CAPACITY outstanding descriptors in this queue.
    /// - ensures: each input descriptor is published exactly once.
    /// - fails: disconnected native channel.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns broken pipe if the native receiver has exited.
    fn publish(
        &mut self,
        items: &[T],
        publication: Publication,
    ) -> io::Result<()>
    {
        let mut remaining = items;
        while !remaining.is_empty() {
            let count = match *self {
                | Self::Channel(ref sender) => {
                    for item in remaining {
                        sender
                            .send(*item)
                            .map_err(|_disconnected| io::Error::from(io::ErrorKind::BrokenPipe))?;
                    }
                    remaining.len()
                },
                | Self::Rtrb(ref mut sender) if publication == Publication::Batch => {
                    // This safe chunks API reserves, fills and commits one chunk.
                    match sender.push_entire_slice(remaining) {
                        | Ok(()) => remaining.len(),
                        | Err(rtrb::chunks::ChunkError::TooFewSlots(_)) => 0,
                    }
                },
                | Self::Ringbuf(ref mut sender) if publication == Publication::Batch => {
                    sender.push_slice(remaining)
                },
                | Self::Rtrb(ref mut sender) => {
                    let item = remaining.first().ok_or(io::ErrorKind::InvalidData)?;
                    match sender.push(*item) {
                        | Ok(()) => 1,
                        | Err(rtrb::PushError::Full(_)) => 0,
                    }
                },
                | Self::Ringbuf(ref mut sender) => {
                    let item = remaining.first().ok_or(io::ErrorKind::InvalidData)?;
                    match sender.try_push(*item) {
                        | Ok(()) => 1,
                        | Err(_) => 0,
                    }
                },
            };
            remaining = remaining.get(count ..).ok_or(io::ErrorKind::InvalidData)?;
            if count == 0 {
                core::hint::spin_loop();
            }
        }
        Ok(())
    }
}

/// A consumer, including the worker-owned work-stealing state.
enum Receive<T>
{
    /// Native channel.
    Channel(crossbeam_channel::Receiver<T>),
    /// Wait-free ring.
    Rtrb(rtrb::Consumer<T>),
    /// Cached lock-free ring.
    Ringbuf(ringbuf::HeapCons<T>),
    /// Worker-local deque and shared stealing handles.
    Steal
    {
        /// Only this worker pops from its local deque.
        local: crossbeam_deque::Worker<T>,
        /// Initial publication queue.
        injector: Arc<crossbeam_deque::Injector<T>>,
        /// Peer work-stealing handles.
        peers: Vec<crossbeam_deque::Stealer<T>>,
    },
}

impl<T> Receive<T>
where
    T: Copy,
{
    /// Drain currently available descriptors, never waiting for a full chunk.
    ///
    /// # Specification
    /// - ensures: only the returned prefix is initialized by this operation.
    /// - fails: disconnected native channel.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns broken pipe on native channel disconnection.
    fn poll(
        &mut self,
        output: &mut [T],
        publication: Publication,
    ) -> io::Result<Natural>
    {
        if publication == Publication::Batch {
            match *self {
                | Self::Rtrb(ref mut receiver) => {
                    return Ok(Natural(receiver.pop_partial_slice(output).0.len()));
                },
                | Self::Ringbuf(ref mut receiver) => {
                    return Ok(Natural(receiver.pop_slice(output)));
                },
                | _ => {},
            }
        }
        let mut count = 0_usize;
        for slot in output {
            let item = match *self {
                | Self::Channel(ref receiver) => match receiver.try_recv() {
                    | Ok(item) => Some(item),
                    | Err(crossbeam_channel::TryRecvError::Empty) => None,
                    | Err(crossbeam_channel::TryRecvError::Disconnected) => {
                        return Err(io::ErrorKind::BrokenPipe.into());
                    },
                },
                | Self::Rtrb(ref mut receiver) => match receiver.pop() {
                    | Ok(item) => Some(item),
                    | Err(rtrb::PopError::Empty) => None,
                },
                | Self::Ringbuf(ref mut receiver) => receiver.try_pop(),
                | Self::Steal {
                    ref local,
                    ref injector,
                    ref peers,
                } => local
                    .pop()
                    .or_else(|| injector.steal_batch_and_pop(local).success())
                    .or_else(|| peers.iter().find_map(|peer| peer.steal().success())),
            };
            let Some(item) = item
            else {
                break;
            };
            *slot = item;
            count = count.saturating_add(1);
        }
        Ok(Natural(count))
    }

    /// Receive at least one descriptor using the declared waiting policy.
    ///
    /// # Specification
    /// - requires: nonempty output buffer.
    /// - ensures: returns the received prefix length, never an empty chunk.
    /// - fails: disconnected native channel or empty output buffer.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns broken pipe or invalid input.
    fn take(
        &mut self,
        output: &mut [T],
        wire: Wire,
        wake: Wake,
    ) -> io::Result<Natural>
    {
        if let Self::Channel(ref receiver) = *self {
            let slot = output.first_mut().ok_or(io::ErrorKind::InvalidInput)?;
            *slot = receiver
                .recv()
                .map_err(|_disconnected| io::Error::from(io::ErrorKind::BrokenPipe))?;
            return Ok(Natural(1));
        }
        let mut misses = Natural(0);
        loop {
            let count = self.poll(output, wire.publication)?;
            if count.0 != 0 {
                return Ok(count);
            }
            wake.idle(&mut misses);
        }
    }
}

/// Equal-capacity endpoints; upstream cache padding separates shared indices.
///
/// # Specification
/// - ensures: returns the two ends of one selected queue.
/// - panics: none; the fixed capacity is positive and representable.
fn pair<T>(kind: Kind) -> (Send<T>, Receive<T>)
{
    match kind {
        | Kind::Rtrb(_) => {
            let (sender, receiver) = rtrb::RingBuffer::new(CAPACITY);
            (Send::Rtrb(sender), Receive::Rtrb(receiver))
        },
        | Kind::Ringbuf(_) => {
            let (sender, receiver) = ringbuf::HeapRb::new(CAPACITY).split();
            (Send::Ringbuf(sender), Receive::Ringbuf(receiver))
        },
        | Kind::Channel | Kind::Steal => {
            let (sender, receiver) = crossbeam_channel::bounded(CAPACITY);
            (Send::Channel(sender), Receive::Channel(receiver))
        },
    }
}

/// Preallocated job shards, prepared before timing.
pub(super) struct Wave
{
    /// One shared vector or one vector per SPSC worker.
    shards: Vec<Vec<Command>>,
    /// Expected receipt count.
    count: Natural,
}

/// Parent-owned ends and notification handles for a standing pool.
pub(super) struct Pool
{
    /// One MPMC sender or one SPSC sender per worker.
    jobs: Vec<Send<Command>>,
    /// One MPMC receiver or one SPSC receiver per worker.
    results: Vec<Receive<Receipt>>,
    /// Used only for work stealing.
    injector: Arc<crossbeam_deque::Injector<Command>>,
    /// Worker notification handles.
    workers: Vec<thread::Thread>,
    /// Publication and drain parameters.
    wire: Wire,
    /// Waiting policy.
    wake: Wake,
}

impl Pool
{
    /// Partition Copy descriptors without any timed allocation or routing copy.
    ///
    /// # Specification
    /// - ensures: ring jobs are round-robin; shared queues retain input order.
    /// - panics: none.
    pub(super) fn prepare(
        &self,
        commands: &[Command],
    ) -> Wave
    {
        let count = self.jobs.len().max(1);
        let shards = (0 .. count)
            .map(|worker| {
                commands
                    .iter()
                    .copied()
                    .skip(worker)
                    .step_by(count)
                    .collect()
            })
            .collect();
        Wave {
            shards,
            count: Natural(commands.len()),
        }
    }

    /// Publish a wave, then collect all receipts into caller-reserved storage.
    ///
    /// # Specification
    /// - requires: wave fits CAPACITY; output has capacity for every receipt.
    /// - ensures: success collects exactly the submitted number of receipts.
    /// - fails: native transport disconnection or malformed observer
    ///   coordinates.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the originating I/O failure.
    pub(super) fn exchange(
        &mut self,
        wave: &Wave,
        output: &mut Vec<Receipt>,
    ) -> io::Result<()>
    {
        if self.wire.kind == Kind::Steal {
            for shard in &wave.shards {
                for command in shard {
                    self.injector.push(*command);
                }
            }
        }
        else {
            for (sender, shard) in self.jobs.iter_mut().zip(&wave.shards) {
                sender.publish(shard, self.wire.publication)?;
            }
        }
        for worker in &self.workers {
            self.wake.notify(worker);
        }
        let mut buffer = [Receipt::empty(Natural(0)); 32];
        let mut misses = Natural(0);
        while output.len() < wave.count.0 {
            let before = output.len();
            for receiver in &mut self.results {
                let count = if matches!(self.wire.kind, Kind::Channel | Kind::Steal) {
                    receiver.take(&mut buffer, self.wire, self.wake)?
                }
                else {
                    receiver.poll(&mut buffer, self.wire.publication)?
                };
                let received = buffer.get(.. count.0).ok_or(io::ErrorKind::InvalidData)?;
                output.extend_from_slice(received);
            }
            if output.len() == before {
                self.wake.idle(&mut misses);
            }
            else {
                misses.0 = 0;
            }
        }
        Ok(())
    }
}

/// Run one worker until an explicit stop, retaining its own arena scratch.
///
/// # Specification
/// - ensures: returns a receipt for every non-stop command; never waits to fill
///   k.
/// - fails: transport or observer buffer error.
/// - panics: none.
///
/// # Errors
/// Returns the originating I/O failure.
fn worker(
    mut input: Receive<Command>,
    mut output: Send<Receipt>,
    mut scratch: Scratch<'_>,
    workload: &[Workload],
    wire: Wire,
    parent: &thread::Thread,
    wake: Wake,
) -> io::Result<()>
{
    let mut commands = [Command::Ping(Natural(0)); 32];
    let mut receipts = [Receipt::empty(Natural(0)); 32];
    loop {
        let buffer = commands
            .get_mut(.. wire.drain.0)
            .ok_or(io::ErrorKind::InvalidInput)?;
        let count = input.take(buffer, wire, wake)?;
        let commands = commands.get(.. count.0).ok_or(io::ErrorKind::InvalidData)?;
        for (command, receipt) in commands.iter().zip(&mut receipts) {
            if matches!(command, Command::Stop) {
                return Ok(());
            }
            *receipt = execute(*command, &mut scratch, workload);
        }
        let receipts = receipts.get(.. count.0).ok_or(io::ErrorKind::InvalidData)?;
        output.publish(receipts, wire.publication)?;
        wake.notify(parent);
    }
}

/// Construct and join a standing pool outside the supplied experiment's timers.
///
/// # Specification
/// - requires: positive worker count; tasks do not panic.
/// - ensures: workers stop even if the experiment returns an error.
/// - fails: transport, experiment, or worker panic.
/// - panics: none.
///
/// # Errors
/// Returns the originating I/O error or a named worker-panic error.
///
/// # Adequacy
/// - hypothesis: L2 — every matrix receipt equals its independent serial
///   oracle.
/// - witness: `template::tests::compressed_admission_matches_plain_families`
pub(super) fn standing<F>(
    wire: Wire,
    threads: Threads,
    workload: &[Workload],
    mode: Mode,
    experiment: F,
) -> io::Result<()>
where
    F: FnOnce(&mut Pool) -> io::Result<()>,
{
    let scratch = Scratch::new(workload, mode).map_err(io::Error::other)?;
    thread::scope(|scope| {
        let wake = match wire.kind {
            | Kind::Rtrb(wake) | Kind::Ringbuf(wake) => wake,
            | _ => Wake::Park,
        };
        let injector = Arc::new(crossbeam_deque::Injector::new());
        let locals: Vec<_> = core::iter::repeat_with(crossbeam_deque::Worker::new_fifo)
            .take(threads.0)
            .collect();
        let peers: Vec<_> = locals
            .iter()
            .map(crossbeam_deque::Worker::stealer)
            .collect();
        let (shared_jobs, shared_input) = crossbeam_channel::bounded(CAPACITY);
        let (shared_output, shared_results) = crossbeam_channel::bounded(CAPACITY);
        let mut pool = Pool {
            jobs: Vec::new(),
            results: Vec::new(),
            injector: Arc::clone(&injector),
            workers: Vec::new(),
            wire,
            wake,
        };
        if wire.kind == Kind::Channel {
            pool.jobs.push(Send::Channel(shared_jobs));
        }
        if matches!(wire.kind, Kind::Channel | Kind::Steal) {
            pool.results.push(Receive::Channel(shared_results));
        }
        let ready = Arc::new(std::sync::Barrier::new(threads.0.saturating_add(1)));
        let parent = thread::current();
        let mut handles = Vec::new();
        for local in locals {
            let (input, output) = match wire.kind {
                | Kind::Channel => (
                    Receive::Channel(shared_input.clone()),
                    Send::Channel(shared_output.clone()),
                ),
                | Kind::Steal => (
                    Receive::Steal {
                        local,
                        injector: Arc::clone(&injector),
                        peers: peers.clone(),
                    },
                    Send::Channel(shared_output.clone()),
                ),
                | Kind::Rtrb(_) | Kind::Ringbuf(_) => {
                    let (sender, receiver) = pair(wire.kind);
                    pool.jobs.push(sender);
                    let (output, results) = pair(wire.kind);
                    pool.results.push(results);
                    (receiver, output)
                },
            };
            let scratch = scratch.clone();
            let parent = parent.clone();
            let ready = Arc::clone(&ready);
            let handle = scope.spawn(move || {
                qos();
                ready.wait();
                worker(input, output, scratch, workload, wire, &parent, wake)
            });
            pool.workers.push(handle.thread().clone());
            handles.push(handle);
        }
        qos();
        ready.wait();
        let result = experiment(&mut pool);
        if wire.kind == Kind::Steal {
            for _ in 0 .. threads.0 {
                pool.injector.push(Command::Stop);
            }
        }
        else if wire.kind == Kind::Channel {
            let sender = pool.jobs.first_mut().ok_or(io::ErrorKind::BrokenPipe)?;
            for _ in 0 .. threads.0 {
                sender.publish(&[Command::Stop], Publication::Each)?;
            }
        }
        else {
            for sender in &mut pool.jobs {
                sender.publish(&[Command::Stop], Publication::Each)?;
            }
        }
        for worker in &pool.workers {
            worker.unpark();
        }
        for handle in handles {
            let joined = handle
                .join()
                .map_err(|_panic| io::Error::other("observer worker panicked"))?;
            joined?;
        }
        result
    })
}

#[cfg(target_os = "macos")]
unsafe extern "C" {
    /// Darwin's per-thread quality-of-service request.
    safe fn pthread_set_qos_class_self_np(
        class: u32,
        relative: i32,
    ) -> i32;
}

/// Research: request user-interactive QoS when `GANDR_QOS` is set, biasing
/// the thread onto performance cores.
///
/// # Specification
/// trivial.
fn qos()
{
    #[cfg(target_os = "macos")]
    if std::env::var("GANDR_QOS").is_ok() {
        let _status: i32 = pthread_set_qos_class_self_np(0x21, 0);
    }
}
