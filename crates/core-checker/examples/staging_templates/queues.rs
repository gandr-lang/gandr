//! Observer transports: padded upstream rings, equal capacities, no kernel
//! dependency.

use alloc::sync::Arc;
use std::thread;

use anodized::spec;
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
    ///   polls and restarts its miss count.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — parking workers that miss a wake token stall the
    ///   pooled exchanges; busy workers that park stall them likewise.
    /// - witness: `admission::handoff::tests::pooled_receipts_equal_the_serial_oracle`
    #[spec(
        captures: before = misses.0,
        ensures: |()| if self == Self::Park && before >= 64 {
            misses.0 == 0
        }
        else {
            misses.0 == before.saturating_add(1)
        },
    )]
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

/// Whether the dispatcher executes a share of a wave while workers run.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Share
{
    /// Publish every shard to workers, then poll the result rings.
    Spin,
    /// Keep one round-robin shard, execute it, then poll the result rings.
    Work,
}

impl Share
{
    /// Stable measurement label.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn label(self) -> Label
    {
        Label(match self {
            | Self::Spin => "spin",
            | Self::Work => "work",
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
    /// Whether the dispatcher executes a shard of each wave.
    pub share: Share,
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
    /// - executable: none — the published descriptors are observable only at
    ///   the receiving endpoint, which this call does not hold.
    ///
    /// # Errors
    /// Returns broken pipe if the native receiver has exited.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a lost or repeated descriptor changes the receipts
    ///   every pooled exchange compares with its serial oracle.
    /// - witness: `admission::handoff::tests::pooled_receipts_equal_the_serial_oracle`
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a count past the received prefix replays stale
    ///   receipts, which the serial oracle refuses.
    /// - witness: `admission::handoff::tests::pooled_receipts_equal_the_serial_oracle`
    #[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|count| count.0 <= output.len()))]
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
        for slot in output.iter_mut() {
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — an empty chunk would stall a worker; a long one would
    ///   replay stale descriptors.
    /// - witness: `admission::handoff::tests::pooled_receipts_equal_the_serial_oracle`
    #[spec(
        requires: !output.is_empty(),
        ensures: |ret| ret.as_ref().ok().is_none_or(|count| count.0 >= 1 && count.0 <= output.len()),
    )]
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
///
/// # Adequacy
/// - hypothesis: L2 — every ring kind runs the pooled differential.
/// - witness: `admission::handoff::tests::pooled_receipts_equal_the_serial_oracle`
#[spec(ensures: |ret| matches!((kind, &ret),
    (Kind::Rtrb(_), &(Send::Rtrb(_), Receive::Rtrb(_)))
    | (Kind::Ringbuf(_), &(Send::Ringbuf(_), Receive::Ringbuf(_)))
    | (Kind::Channel | Kind::Steal, &(Send::Channel(_), Receive::Channel(_)))))]
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
pub(super) struct Pool<'schema>
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
    /// The dispatcher's own scratch, used only under `Share::Work`.
    own: Scratch<'schema>,
    /// The families every task indexes.
    workload: &'schema [Workload],
}

impl Pool<'_>
{
    /// Partition Copy descriptors without any timed allocation or routing copy.
    ///
    /// # Specification
    /// - ensures: ring jobs are round-robin; shared queues retain input order;
    ///   under `Share::Work` the last round-robin shard is the dispatcher's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a dropped or doubled descriptor changes the pooled
    ///   receipts; a missing dispatcher shard stalls `Share::Work`.
    /// - witness: `admission::handoff::tests::pooled_receipts_equal_the_serial_oracle`
    #[spec(ensures: |ret| ret.count.0 == commands.len()
        && ret.shards.len() == self.jobs.len().max(1).saturating_add(usize::from(self.wire.share == Share::Work))
        && ret.shards.iter().map(Vec::len).sum::<usize>() == commands.len())]
    pub(super) fn prepare(
        &self,
        commands: &[Command],
    ) -> Wave
    {
        let count = self
            .jobs
            .len()
            .max(1)
            .saturating_add(usize::from(self.wire.share == Share::Work));
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

    /// Publish a wave, execute the dispatcher's shard when it takes one, then
    /// collect all receipts into caller-reserved storage.
    ///
    /// # Specification
    /// - requires: wave fits CAPACITY; output is empty and has capacity for
    ///   every receipt.
    /// - ensures: success collects exactly the submitted number of receipts.
    /// - fails: native transport disconnection or malformed observer
    ///   coordinates.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the originating I/O failure.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every exchange's receipts are verified against the
    ///   serial oracle after collection.
    /// - witness: `admission::handoff::tests::pooled_receipts_equal_the_serial_oracle`
    #[spec(
        requires: output.is_empty(),
        ensures: |ret| ret.is_err() || output.len() == wave.count.0,
    )]
    pub(super) fn exchange(
        &mut self,
        wave: &Wave,
        output: &mut Vec<Receipt>,
    ) -> io::Result<()>
    {
        let (remote, local) = match (self.wire.share, wave.shards.split_last()) {
            | (Share::Work, Some((local, remote))) => (remote, local.as_slice()),
            | (Share::Work | Share::Spin, _) => (wave.shards.as_slice(), [].as_slice()),
        };
        if self.wire.kind == Kind::Steal {
            for shard in remote {
                for command in shard {
                    self.injector.push(*command);
                }
            }
        }
        else {
            for (sender, shard) in self.jobs.iter_mut().zip(remote) {
                sender.publish(shard, self.wire.publication)?;
            }
        }
        for worker in &self.workers {
            self.wake.notify(worker);
        }
        for command in local {
            output.push(execute(*command, &mut self.own, self.workload));
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
/// - executable: none — the receipts go to the dispatcher's endpoint, which
///   this thread does not hold.
///
/// # Errors
/// Returns the originating I/O failure.
///
/// # Adequacy
/// - hypothesis: L2 — a missing receipt stalls the exchange; a changed one
///   fails the serial-oracle comparison.
/// - witness: `admission::handoff::tests::pooled_receipts_equal_the_serial_oracle`
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
/// - hypothesis: L2 — every transport's receipts equal their independent serial
///   oracle, refusals included.
/// - witness: `admission::handoff::tests::pooled_receipts_equal_the_serial_oracle`
#[spec(requires: threads.0 > 0)]
pub(super) fn standing<'schema, F>(
    wire: Wire,
    threads: Threads,
    workload: &'schema [Workload],
    mode: Mode,
    experiment: F,
) -> io::Result<()>
where
    F: FnOnce(&mut Pool<'schema>) -> io::Result<()>,
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
            own: scratch.clone(),
            workload,
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
                ready.wait();
                worker(input, output, scratch, workload, wire, &parent, wake)
            });
            pool.workers.push(handle.thread().clone());
            handles.push(handle);
        }
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
