//! The interface: a buffer moves into each submission and comes back with
//! its completion, one completion for each submission, in the ring's form
//! or in the blocking form. Each buffer lives in the allocator that the
//! caller names; a worker names its region.

use alloc::collections::VecDeque;
use alloc::sync::Arc;
use alloc::sync::Weak;
use alloc::vec::Vec;
use core::alloc::Allocator;
use core::sync::atomic::AtomicU64;
use core::sync::atomic::Ordering;
use std::fs::File;
use std::os::fd::AsFd as _;
use std::sync::OnceLock;

use crate::blocking::Blocking;
use crate::buffer::Buffer;
use crate::buffer::FileSlot;
use crate::buffer::Table;
use crate::faults::Fault;
use crate::faults::Faults;
use crate::faults::Injected;
use crate::faults::Odds;
use crate::faults::Seed;
use crate::ring::Count;
use crate::ring::Entry;
use crate::ring::Key;
use crate::ring::Moved;
use crate::ring::Position;
use crate::ring::Ring;
use crate::sys;
use crate::sys::Errno;

/// The slots of a ring's table of fixed files: the files that one worker
/// names by slot at once. [`Io::fix`] refuses a file past them, and the
/// file's own handle runs by its descriptor.
pub const FILES: u32 = 64;

/// The bytes of the smallest page on x86-64, aarch64 and riscv64: the kernel
/// pins a registered buffer by whole pages.
const PAGE: u64 = 4_096;

/// The bytes that the crate's rings pin in the process, which the limit of
/// locked memory bounds.
static PINNED: AtomicU64 = AtomicU64::new(0);

/// The process's limit of locked memory in bytes, read at the first
/// registration; `u64::MAX` for no limit.
static LOCKED: OnceLock<u64> = OnceLock::new();

/// A count of bytes that a ring pins.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Pinned(u64);

impl Pinned
{
    /// The buffers of `each` bytes, up to `count`, that fit in the room that
    /// `limit` leaves past `held`.
    ///
    /// # Specification
    /// - ensures: `ret` is at most `count`, and `ret` buffers of `each` bytes
    ///   added to `held` stay within `limit`; one more would not, unless `ret`
    ///   is `count`.
    /// - panics: none.
    /// - executable: none — a counting argument the witness checks at the
    ///   edges.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — 8 MiB of room fits 32 buffers of 256 KiB and not 33,
    ///   and no room fits none.
    /// - witness: `io::tests::a_reservation_fits_within_the_limit`
    fn fit(
        limit: Self,
        held: Self,
        count: Count,
        each: Self,
    ) -> Count
    {
        let fit = limit
            .0
            .saturating_sub(held.0)
            .checked_div(each.0)
            .unwrap_or(u64::MAX)
            .min(u64::from(u32::from(count)));
        Count::from(u32::try_from(fit).unwrap_or(u32::MAX))
    }

    /// Take room for up to `count` buffers of `each` bytes within the
    /// process's limit of locked memory, which the first call reads: the
    /// buffers that fit, and their bytes, which [`Pinned::release`] gives
    /// back.
    ///
    /// # Specification
    /// - ensures: the bytes that the crate's rings hold stay within the limit,
    ///   whatever threads reserve at once.
    /// - panics: none.
    /// - executable: none — the limit is the kernel's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Pinned::fit`].
    /// - witness: `io::tests::a_reservation_fits_within_the_limit`
    fn reserve(
        count: Count,
        each: Self,
    ) -> (Count, Self)
    {
        let limit = Self(*LOCKED.get_or_init(|| {
            sys::locked().ok().flatten().map_or(u64::MAX, |bytes| {
                u64::try_from(usize::from(bytes)).unwrap_or(u64::MAX)
            })
        }));
        let mut held = PINNED.load(Ordering::Relaxed);
        loop {
            let fit = Self::fit(limit, Self(held), count, each);
            let bytes = each.0.saturating_mul(u64::from(u32::from(fit)));
            match PINNED.compare_exchange_weak(
                held,
                held.saturating_add(bytes),
                Ordering::AcqRel,
                Ordering::Relaxed,
            ) {
                Ok(_before) => return (fit, Self(bytes)),
                Err(now) => held = now,
            }
        }
    }

    /// Give back the bytes that a reservation took.
    ///
    /// # Specification
    /// trivial.
    fn release(self)
    {
        let _before = PINNED.fetch_sub(self.0, Ordering::AcqRel);
    }
}

/// How many buffers of a registration the ring fixes.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Pinning
{
    /// The ring fixes each buffer.
    Whole,
    /// The ring fixes this many buffers, the first ones: the process's limit
    /// of locked memory holds no more, and the rest run unregistered.
    Within(Count),
    /// The kernel refused the registration with this error number, and each
    /// buffer runs unregistered.
    Refused(Errno),
    /// The blocking form fixes no buffer.
    Blocking,
}

/// The buffers of a registration, and how many of them the ring fixes.
///
/// # Specification
/// trivial.
#[derive(Debug)]
pub struct Registered<A>
where
    A: Allocator,
{
    /// The buffers, the fixed ones first.
    pub buffers: Vec<Buffer<A>, A>,
    /// How many of them the ring fixes.
    pub pinning: Pinning,
}

/// The form that an [`Io`] runs under. A run reports it, and no consumer
/// branches on it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Form
{
    /// The kernel's `io_uring`.
    Ring,
    /// Positioned calls on the worker's own thread.
    Blocking,
}

impl Form
{
    /// The form that a refusal of the ring's setup leaves: the blocking form
    /// for a refusal of permission, a kernel with no `io_uring_setup`, a
    /// ring without stable submissions, or a ring that breaks its protocol.
    /// Any other refusal is an error.
    ///
    /// # Specification
    /// - ensures: `Ok(Form::Blocking)` for [`Errno::PERMISSION`],
    ///   [`Errno::NO_SYSTEM_CALL`], [`Errno::NOT_SUPPORTED`] and
    ///   [`Errno::PROTOCOL`]; `Err(refusal)` for any other.
    /// - panics: none.
    /// - executable: none — the predicate repeats the body's four comparisons.
    ///
    /// # Errors
    /// The refusal itself, when it is none of the four.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a container that refuses the ring runs the blocking
    ///   form, and an exhausted kernel stops the run.
    /// - witness: `tests::io::the_blocking_form_follows_a_refusal_of_the_ring`
    #[inline]
    pub fn after(refusal: Errno) -> Result<Self, Errno>
    {
        if refusal == Errno::PERMISSION
            || refusal == Errno::NO_SYSTEM_CALL
            || refusal == Errno::NOT_SUPPORTED
            || refusal == Errno::PROTOCOL
        {
            Ok(Self::Blocking)
        }
        else {
            Err(refusal)
        }
    }
}

/// A file that an [`Io`] reads and writes.
///
/// Each submission holds a share of the file until its completion, so the
/// descriptor stays open while the kernel or the thread uses it. A handle
/// that [`Io::fix`] gives carries its slot in that ring's table of fixed
/// files. That ring names the file by the slot, and any other `Io` by its
/// descriptor, so a slot never leaves its ring bare.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
pub struct Handle
{
    /// The file.
    file: Arc<File>,
    /// The file's slot in one ring's table of fixed files, with that table.
    fixed: Option<(Table, FileSlot)>,
}

impl From<File> for Handle
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(file: File) -> Self
    {
        Self {
            file: Arc::new(file),
            fixed: None,
        }
    }
}

impl Handle
{
    /// The file.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn file(&self) -> &File
    {
        &self.file
    }

    /// The file's slot in `table`, when that table holds it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn slot_in(
        &self,
        table: Table,
    ) -> Option<FileSlot>
    {
        let (held, slot) = self.fixed?;
        (held == table).then_some(slot)
    }
}

/// A file that a worker appends to: its handle, and its end. Each append
/// writes at the end and moves the end past the bytes it submits.
///
/// # Specification
/// trivial.
#[derive(Debug)]
pub struct Segment
{
    /// The file.
    handle: Handle,
    /// The position of the next append.
    end: Position,
}

impl Segment
{
    /// A segment of `handle` whose next append writes at `end`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        handle: Handle,
        end: Position,
    ) -> Self
    {
        Self { handle, end }
    }

    /// The segment's file.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn handle(&self) -> &Handle
    {
        &self.handle
    }

    /// The position of the next append.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn end(&self) -> Position
    {
        self.end
    }
}

/// Whether the next submission depends on this one.
///
/// A linked submission's successor starts only after it succeeds, and
/// completes cancelled when it fails. A chain ends where the [`Io`]
/// submits: at [`Io::submit`], at [`Io::wait`], and where a full [`Io`]
/// parks.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Chain
{
    /// The next submission does not depend on this one.
    Alone,
    /// The next submission starts only after this one succeeds.
    Linked,
}

/// A submission that the [`Io`] holds, and the key of its completion.
///
/// # Specification
/// trivial.
#[must_use]
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Pending(Key);

/// The end of one submission: its pending key, the bytes it moved or the
/// error number it failed with, the position it read or wrote at, and the
/// buffer it took, given back.
///
/// # Specification
/// trivial.
pub struct Done<A>
where
    A: Allocator,
{
    /// The submission that completes.
    pub pending: Pending,
    /// The bytes moved, or the error number.
    pub outcome: Result<Moved, Errno>,
    /// The position read or written at: for an append, the position it
    /// wrote at.
    pub at: Position,
    /// The buffer that the submission took, for a read or a write.
    pub buffer: Option<Buffer<A>>,
}

impl<A> core::fmt::Debug for Done<A>
where
    A: Allocator,
{
    /// Each field, whatever the allocator.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.debug_struct("Done")
            .field("pending", &self.pending)
            .field("outcome", &self.outcome)
            .field("at", &self.at)
            .field("buffer", &self.buffer)
            .finish()
    }
}

/// Why the [`Io`] refuses a submission or a registration.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Reason
{
    /// The caller holds as many completions unread as the [`Io`] keeps: it
    /// takes one with [`Io::wait`] before it submits again.
    Unread,
    /// The kernel refused the submission of the staged entries. A refused
    /// registration is no refusal: [`Pinning::Refused`] names it.
    Kernel(Errno),
    /// The caller's allocator refused the bytes of a registration: a
    /// region's budget holds no more.
    Budget,
}

/// A refused submission, with the buffer it would have taken.
///
/// # Specification
/// trivial.
pub struct Refused<A>
where
    A: Allocator,
{
    /// Why the [`Io`] refuses it.
    pub reason: Reason,
    /// The buffer, given back.
    pub buffer: Option<Buffer<A>>,
}

impl<A> core::fmt::Debug for Refused<A>
where
    A: Allocator,
{
    /// Each field, whatever the allocator.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.debug_struct("Refused")
            .field("reason", &self.reason)
            .field("buffer", &self.buffer)
            .finish()
    }
}

/// What a submission does, with what it holds until its completion.
///
/// # Specification
/// trivial.
#[derive(Debug)]
pub enum Operation<A>
where
    A: Allocator,
{
    /// A read into `buffer` from the handle's file.
    Read
    {
        /// The file.
        handle: Handle,
        /// The bytes to read into.
        buffer: Buffer<A>,
    },
    /// A write of `buffer` into the handle's file.
    Write
    {
        /// The file.
        handle: Handle,
        /// The bytes to write.
        buffer: Buffer<A>,
    },
    /// A sync of the handle's file.
    Sync
    {
        /// The file.
        handle: Handle,
    },
    /// A cancel of the submission keyed `target`.
    Cancel
    {
        /// The submission to cancel.
        target: Key,
    },
}

impl<A> Operation<A>
where
    A: Allocator,
{
    /// The buffer that the operation holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_buffer(self) -> Option<Buffer<A>>
    {
        match self {
            Self::Read { buffer, .. } | Self::Write { buffer, .. } => Some(buffer),
            Self::Sync { .. } | Self::Cancel { .. } => None,
        }
    }

    /// The count of bytes that the operation asks to move.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn asked(&self) -> Moved
    {
        match *self {
            Self::Read { ref buffer, .. } | Self::Write { ref buffer, .. } => buffer.length(),
            Self::Sync { .. } | Self::Cancel { .. } => Moved::from(0),
        }
    }
}

/// Whether an order still runs, or a cancel stopped it before it started.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Fate
{
    /// The order runs.
    Run,
    /// A cancel stopped the order before it started.
    Cancelled,
}

/// One submission as a form holds it.
///
/// # Specification
/// trivial.
#[derive(Debug)]
pub struct Order<A>
where
    A: Allocator,
{
    /// The key of its completion.
    pub key: Key,
    /// The position it reads or writes at.
    pub at: Position,
    /// Whether the next order depends on it.
    pub chain: Chain,
    /// Whether it still runs.
    pub fate: Fate,
    /// What it does.
    pub operation: Operation<A>,
    /// The fault that an `Io` with faults drew for it.
    pub fault: Option<Injected>,
}

impl<A> Order<A>
where
    A: Allocator,
{
    /// The completion of this order with `outcome`, which gives its buffer
    /// back. A corrupt read flips its byte here, under each form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn done(
        self,
        outcome: Result<Moved, Errno>,
    ) -> Done<A>
    {
        let mut buffer = self.operation.into_buffer();
        if let (Some(Injected::Corrupt(byte)), Ok(_), Some(read)) =
            (self.fault, outcome, buffer.as_mut())
        {
            read.flip(byte);
        }
        Done {
            pending: Pending(self.key),
            outcome,
            at: self.at,
            buffer,
        }
    }

    /// The position the order moves its bytes at: a misdirected write lands
    /// elsewhere.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn landing(&self) -> Position
    {
        match self.fault {
            Some(Injected::Misdirected(at)) => at,
            Some(Injected::Torn(_) | Injected::Lost | Injected::Corrupt(_)) | None => self.at,
        }
    }

    /// The bytes the order moves of `asked`: a torn write keeps a prefix.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn kept(
        &self,
        asked: Moved,
    ) -> Moved
    {
        match self.fault {
            Some(Injected::Torn(kept)) => Moved::from(u32::from(kept).min(u32::from(asked))),
            Some(Injected::Lost | Injected::Misdirected(_) | Injected::Corrupt(_)) | None => asked,
        }
    }

    /// The ring's entry for this order, over the buffer that the order
    /// holds. A buffer that `table` registers reads and writes by its slot,
    /// and a file that `table` holds is named by its slot.
    ///
    /// # Specification
    /// trivial.
    fn entry(
        &mut self,
        table: Table,
    ) -> Entry
    {
        let at = self.landing();
        let (entry, slot) = match self.operation {
            Operation::Read {
                ref handle,
                ref mut buffer,
            } => (
                Entry::read(handle.file.as_fd(), buffer, table, at, self.key),
                handle.slot_in(table),
            ),
            Operation::Write {
                ref handle,
                ref buffer,
            } => {
                let kept = self.kept(buffer.length());
                (
                    Entry::write(handle.file.as_fd(), buffer, table, at, self.key).limited(kept),
                    handle.slot_in(table),
                )
            },
            Operation::Sync { ref handle } => (
                Entry::sync(handle.file.as_fd(), self.key),
                handle.slot_in(table),
            ),
            Operation::Cancel { target } => (Entry::cancel(target, self.key), None),
        };
        let entry = slot.map_or(entry, |slot| entry.by_slot(slot));
        match self.chain {
            Chain::Alone => entry,
            Chain::Linked => entry.linked(),
        }
    }
}

/// The ring's form: the ring, the orders that the kernel holds, each with
/// its buffer and its file until its completion, and the files that its
/// table of fixed files holds.
struct Uring<A>
where
    A: Allocator,
{
    /// The ring.
    ring: Ring,
    /// The orders that the kernel holds.
    flight: Vec<Order<A>>,
    /// The file in each slot of the ring's table of fixed files, empty
    /// until the first [`Io::fix`]. A slot whose file no handle holds
    /// takes the next file fixed.
    files: Vec<Weak<File>>,
    /// The bytes that the ring's table of fixed buffers pins.
    pinned: Pinned,
}

impl<A> Uring<A>
where
    A: Allocator,
{
    /// Push each staged order that the ring takes, and submit them.
    ///
    /// # Specification
    /// - ensures: each order that the ring takes moves from `staged` to the
    ///   kernel, in order; an order it does not take stays in `staged`.
    /// - fails: the kernel's error number from the submission; the pushed
    ///   orders stay with the kernel, and the next submission carries them.
    /// - panics: none.
    /// - executable: none — the queue is shared with the kernel.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a write, a sync and a read, flushed in one batch,
    ///   complete in order.
    /// - witness: `tests::io::a_linked_write_sync_and_read_complete_in_order`
    fn flush(
        &mut self,
        staged: &mut Vec<Order<A>>,
    ) -> Result<(), Errno>
    {
        let mut pushed = 0_usize;
        let table = self.ring.table();
        for order in staged.iter_mut() {
            let entry = order.entry(table);
            // SAFETY: the order moves into `flight` below, and a move of an
            // order leaves its buffer's bytes in place. `flight` keeps the
            // buffer and the file until the order's completion, and the drop
            // waits for each completion.
            let taken = unsafe { self.ring.push(entry) };
            if taken.is_err() {
                break;
            }
            pushed = pushed.saturating_add(1);
        }
        self.flight.extend(staged.drain(.. pushed));
        self.ring.submit(Count::from(0_u32)).map(|_consumed| ())
    }

    /// The next completion that stands, with its order's buffer.
    ///
    /// # Specification
    /// trivial.
    fn take(&mut self) -> Option<Done<A>>
    {
        let completion = self.ring.complete()?;
        let index = self
            .flight
            .iter()
            .position(|order| order.key == completion.key)?;
        Some(self.flight.swap_remove(index).done(completion.outcome))
    }

    /// The next completion, parked in the kernel until one stands.
    ///
    /// # Specification
    /// - ensures: on `Ok`, one completion of an order that the kernel held.
    /// - fails: the kernel's error number, other than an interruption, which
    ///   waits again.
    /// - panics: none.
    /// - executable: none — the queue is shared with the kernel.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a full `Io` parks until a write completes, and never
    ///   spins.
    /// - witness: `tests::io::a_full_io_parks_and_gives_back_what_it_cannot_hold`
    fn wait(&mut self) -> Result<Done<A>, Errno>
    {
        loop {
            if let Some(done) = self.take() {
                return Ok(done);
            }
            match self.ring.submit(Count::from(1_u32)) {
                Ok(_consumed) => {},
                Err(errno) if errno == Errno::INTERRUPTED => {},
                Err(errno) => return Err(errno),
            }
        }
    }
}

impl<A> Drop for Uring<A>
where
    A: Allocator,
{
    /// Wait for each order that the kernel holds, so the kernel writes into
    /// no buffer after it is freed, and give back the bytes that the ring
    /// pinned. A ring that the kernel stops answering leaks the buffers it
    /// holds.
    ///
    /// # Specification
    /// trivial.
    fn drop(&mut self)
    {
        self.pinned.release();
        while !self.flight.is_empty() {
            if self.take().is_some() {
                continue;
            }
            match self.ring.submit(Count::from(1_u32)) {
                Ok(_consumed) => {},
                Err(errno) if errno == Errno::INTERRUPTED => {},
                Err(_errno) => {
                    let _leaked: &mut [Order<A>] = core::mem::take(&mut self.flight).leak();
                    return;
                },
            }
        }
    }
}

/// The form that an [`Io`] runs, with its state.
#[expect(
    clippy::large_enum_variant,
    reason = "one engine for each Io and one Io for each worker: a box would add a load to each operation to save bytes once per thread"
)]
enum Engine<A>
where
    A: Allocator,
{
    /// The kernel's `io_uring`.
    Ring(Uring<A>),
    /// Positioned calls on the worker's own thread.
    Blocking(Blocking<A>),
}

impl<A> Engine<A>
where
    A: Allocator,
{
    /// Hand each staged order to the form.
    ///
    /// # Specification
    /// trivial.
    fn flush(
        &mut self,
        staged: &mut Vec<Order<A>>,
    ) -> Result<(), Errno>
    {
        match *self {
            Self::Ring(ref mut uring) => uring.flush(staged),
            Self::Blocking(ref mut blocking) => {
                blocking.flush(staged);
                Ok(())
            },
        }
    }

    /// The next completion, parked until one stands. The blocking form
    /// holds each completion of what it ran, so it never parks.
    ///
    /// # Specification
    /// - ensures: on `Ok`, one completion of an order that the form held.
    /// - fails: the kernel's error number; [`Errno::PROTOCOL`] when the
    ///   blocking form holds no completion, which the `Io`'s count of what it
    ///   flushed rules out.
    /// - panics: none.
    /// - executable: none — the completions are the kernel's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a full `Io` parks until a write completes, under each
    ///   form.
    /// - witness: `tests::io::a_full_io_parks_and_gives_back_what_it_cannot_hold`
    fn wait(&mut self) -> Result<Done<A>, Errno>
    {
        match *self {
            Self::Ring(ref mut uring) => uring.wait(),
            Self::Blocking(ref mut blocking) => blocking.take().ok_or(Errno::PROTOCOL),
        }
    }

    /// The next completion that stands, if one does.
    ///
    /// # Specification
    /// trivial.
    fn take(&mut self) -> Option<Done<A>>
    {
        match *self {
            Self::Ring(ref mut uring) => uring.take(),
            Self::Blocking(ref mut blocking) => blocking.take(),
        }
    }
}

/// One worker's IO, whose buffers live in the allocator `A`.
///
/// It holds at most `depth` submissions in flight, and at most `2 × depth`
/// completions that the caller has not taken. A buffer moves into each
/// submission and comes back with its completion.
pub struct Io<A>
where
    A: Allocator,
{
    /// The form, with its state.
    engine: Engine<A>,
    /// The most submissions in flight, staged ones counted.
    depth: usize,
    /// The submissions that no form holds yet.
    staged: Vec<Order<A>>,
    /// The submissions that the form holds, without their completions.
    flushed: usize,
    /// The completions that the caller has not taken.
    unread: VecDeque<Done<A>>,
    /// The key of the next submission.
    next: u64,
    /// The draws of the simulator of faults, if the `Io` runs under it.
    faults: Option<Faults>,
}

impl<A> Io<A>
where
    A: Allocator,
{
    /// An `Io` of `depth` submissions in flight, in the ring's form where
    /// the kernel gives a ring, and in the blocking form where it refuses
    /// one as [`Form::after`] reads the refusal.
    ///
    /// # Specification
    /// - ensures: on `Ok`, an `Io` that holds nothing, whose form is the ring's
    ///   when the kernel set one up.
    /// - fails: [`Errno::INVALID`] for a depth of zero; a refusal of the ring
    ///   that [`Form::after`] reads as an error.
    /// - panics: none.
    /// - executable: none — the ring is a kernel object.
    ///
    /// # Errors
    /// [`Errno::INVALID`] for a depth of zero, and the kernel's error where
    /// neither form starts.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the `Io` that this opens completes a linked write,
    ///   sync and read in order.
    /// - witness: `tests::io::a_linked_write_sync_and_read_complete_in_order`
    #[inline]
    pub fn open(depth: Count) -> Result<Self, Errno>
    {
        if u32::from(depth) == 0 {
            return Err(Errno::INVALID);
        }
        match Ring::new(depth) {
            Ok(ring) => Ok(Self::with(
                Engine::Ring(Uring {
                    ring,
                    flight: Vec::new(),
                    files: Vec::new(),
                    pinned: Pinned(0),
                }),
                depth,
            )),
            Err(refusal) => {
                Form::after(refusal)?;
                Self::blocking(depth)
            },
        }
    }

    /// An `Io` of `depth` submissions in flight in the blocking form.
    ///
    /// # Specification
    /// - ensures: on `Ok`, an `Io` that holds nothing, in the blocking form.
    /// - fails: [`Errno::INVALID`] for a depth of zero.
    /// - panics: none.
    /// - executable: none — the form holds no kernel object.
    ///
    /// # Errors
    /// [`Errno::INVALID`] for a depth of zero.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the blocking form completes a linked write, sync and
    ///   read in order, as the ring does.
    /// - witness: `tests::io::a_linked_write_sync_and_read_complete_in_order`
    #[inline]
    pub fn blocking(depth: Count) -> Result<Self, Errno>
    {
        if u32::from(depth) == 0 {
            return Err(Errno::INVALID);
        }
        Ok(Self::with(Engine::Blocking(Blocking::new(depth)), depth))
    }

    /// `count` buffers of `length` bytes each in `allocator`. The ring's
    /// form registers as many of them as the process's limit of locked
    /// memory holds as its table of fixed buffers, and says how many in
    /// [`Registered::pinning`]. The rest come back unregistered. A refusal
    /// for memory halves the table until the kernel takes it, since the
    /// kernel counts each process of the user against the one limit. Any
    /// other refusal leaves each buffer unregistered. Each buffer moves into
    /// a read or a write as any buffer does; the ring reads and writes a
    /// fixed one by its slot. The blocking form registers nothing.
    ///
    /// # Specification
    /// - ensures: on `Ok`, `count` buffers of `length` zero bytes each in
    ///   `allocator`. Under the ring's form, the first buffers carry their
    ///   slots, as many as [`Pinning`] states, and the bytes that the crate's
    ///   rings pin stay within the limit that the start read.
    /// - fails: [`Reason::Budget`] when `allocator` refuses the bytes.
    /// - panics: none.
    /// - executable: none — the registration is the kernel's.
    ///
    /// # Errors
    /// [`Refused`] with no buffer, for a refused allocation.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a registered buffer carries a write and a read under
    ///   each form, an allocator that holds one buffer refuses two, and a
    ///   refused registration gives buffers that carry the same write and read.
    /// - witness: `tests::io::a_registered_buffer_carries_a_fixed_write_and_read`
    /// - witness: `tests::io::a_register_past_the_budget_is_refused`
    /// - witness: `tests::io::a_refused_registration_runs_its_buffers_unregistered`
    #[inline]
    pub fn register(
        &mut self,
        count: Count,
        length: Moved,
        allocator: A,
    ) -> Result<Registered<A>, Refused<A>>
    where
        A: Clone,
    {
        let budget = Refused {
            reason: Reason::Budget,
            buffer: None,
        };
        let width = usize::try_from(u32::from(count)).unwrap_or(usize::MAX);
        let mut buffers = Vec::new_in(allocator.clone());
        if buffers.try_reserve_exact(width).is_err() {
            return Err(budget);
        }
        for _slot in 0 .. width {
            let Some(buffer) = Buffer::zeroed(length, allocator.clone())
            else {
                return Err(budget);
            };
            buffers.push(buffer);
        }
        let Engine::Ring(ref mut uring) = self.engine
        else {
            return Ok(Registered {
                buffers,
                pinning: Pinning::Blocking,
            });
        };
        let each = Pinned(u64::from(u32::from(length)).next_multiple_of(PAGE));
        let (fixed, mut pinned) = Pinned::reserve(count, each);
        let mut chosen = usize::try_from(u32::from(fixed)).unwrap_or(usize::MAX);
        let mut vectors = Vec::new_in(allocator);
        if vectors.try_reserve_exact(chosen).is_err() {
            pinned.release();
            return Err(budget);
        }
        // The kernel counts the pages that each process of the user pins
        // against the one limit, so a table within the process's room can
        // still fail with `ENOMEM`. Each such refusal halves the table.
        let mut refusal = None;
        let pinning = loop {
            let table = match buffers.get_mut(.. chosen) {
                Some(table) if !table.is_empty() => table,
                Some(_) | None => {
                    pinned.release();
                    break refusal
                        .map_or_else(|| Pinning::Within(Count::from(0_u32)), Pinning::Refused);
                },
            };
            match uring.ring.register(table, &mut vectors) {
                Ok(()) => {
                    uring.pinned = Pinned(uring.pinned.0.saturating_add(pinned.0));
                    let held = Count::from(u32::try_from(chosen).unwrap_or(u32::MAX));
                    break if held == count {
                        Pinning::Whole
                    }
                    else {
                        Pinning::Within(held)
                    };
                },
                Err(errno) if errno == Errno::NO_MEMORY => {
                    refusal = Some(errno);
                    let half = chosen.checked_shr(1_u32).unwrap_or_default();
                    let freed = Pinned(each.0.saturating_mul(
                        u64::try_from(chosen.saturating_sub(half)).unwrap_or(u64::MAX),
                    ));
                    freed.release();
                    pinned = Pinned(pinned.0.saturating_sub(freed.0));
                    chosen = half;
                },
                Err(errno) => {
                    pinned.release();
                    break Pinning::Refused(errno);
                },
            }
        };
        Ok(Registered { buffers, pinning })
    }

    /// A handle of `handle`'s file that the ring's form names by a slot of
    /// its table of fixed files, so no entry on it looks the descriptor up.
    /// The blocking form gives the handle as it is. The first call
    /// registers a table of [`FILES`] empty slots. A slot whose file no
    /// handle holds any more takes the next file fixed; the ring keeps that
    /// file open until then.
    ///
    /// # Specification
    /// - ensures: on `Ok`, a handle of the same file; under the ring's form, it
    ///   carries a slot of this ring's table that no live handle holds.
    /// - fails: [`Errno::BUSY`] when each slot holds a file that a handle
    ///   holds; the kernel's error number for a refused registration or update.
    /// - panics: none.
    /// - executable: none — the table is the kernel's.
    ///
    /// # Errors
    /// [`Errno::BUSY`] for a full table; the kernel's error number.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fixed file carries a write, a sync and a read under
    ///   each form, another `Io` reaches it by its descriptor, and the slots of
    ///   dropped handles serve more files than the table holds.
    /// - witness: `tests::io::a_fixed_file_carries_a_write_sync_and_read`
    #[inline]
    pub fn fix(
        &mut self,
        handle: &Handle,
    ) -> Result<Handle, Errno>
    {
        let Engine::Ring(ref mut uring) = self.engine
        else {
            return Ok(handle.clone());
        };
        if uring.files.is_empty() {
            uring.ring.register_files(Count::from(FILES))?;
            uring
                .files
                .resize_with(usize::try_from(FILES).unwrap_or(usize::MAX), Weak::new);
        }
        let (index, held) = uring
            .files
            .iter_mut()
            .enumerate()
            .find(|&(_, ref held)| held.strong_count() == 0)
            .ok_or(Errno::BUSY)?;
        let slot = FileSlot(u32::try_from(index).map_err(|_overflow| Errno::INVALID)?);
        uring.ring.place(slot, handle.file.as_fd())?;
        *held = Arc::downgrade(&handle.file);
        Ok(Handle {
            file: Arc::clone(&handle.file),
            fixed: Some((uring.ring.table(), slot)),
        })
    }

    /// An `Io` over `engine` that holds nothing.
    ///
    /// # Specification
    /// trivial.
    fn with(
        engine: Engine<A>,
        depth: Count,
    ) -> Self
    {
        let width = usize::try_from(u32::from(depth)).unwrap_or(usize::MAX);
        Self {
            engine,
            depth: width,
            staged: Vec::with_capacity(width),
            flushed: 0,
            unread: VecDeque::with_capacity(width.saturating_mul(2)),
            next: 0,
            faults: None,
        }
    }

    /// The form that the `Io` runs under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn form(&self) -> Form
    {
        match self.engine {
            Engine::Ring(_) => Form::Ring,
            Engine::Blocking(_) => Form::Blocking,
        }
    }

    /// This `Io` under the simulator of faults: it draws a fault from `seed`
    /// for one write or read in `odds`, the same draws under each form.
    ///
    /// # Specification
    /// - ensures: the `Io` draws once for each write and each read that it
    ///   stages from now on; [`Io::faults`] logs each fault drawn.
    /// - panics: none.
    /// - executable: none — the faults land in files.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one seed gives one log of faults and one file under
    ///   each form, and the file holds what the log says.
    /// - witness: `tests::faults::a_seed_gives_one_log_and_one_file_under_each_form`
    #[inline]
    #[must_use]
    pub fn with_faults(
        mut self,
        seed: Seed,
        odds: Odds,
    ) -> Self
    {
        self.faults = Some(Faults::new(seed, odds));
        self
    }

    /// Each fault that the simulator drew, in the order of its stage: none
    /// without the simulator.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn faults(&self) -> &[Fault]
    {
        self.faults.as_ref().map_or(&[], Faults::log)
    }

    /// Read from `handle` at `at` into `buffer`, which comes back with the
    /// completion.
    ///
    /// # Specification
    /// - ensures: on `Ok`, the pending key of the read, staged after each
    ///   submission before it.
    /// - fails: [`Refused`], with the buffer, as [`Io::stage`] states.
    /// - panics: none.
    /// - executable: none — the read is the kernel's.
    ///
    /// # Errors
    /// [`Refused`] with the buffer, when the caller holds as many unread
    /// completions as the `Io` keeps, or the kernel refuses a submission.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a read linked after a write and a sync returns the
    ///   bytes written.
    /// - witness: `tests::io::a_linked_write_sync_and_read_complete_in_order`
    #[inline]
    pub fn read_at(
        &mut self,
        handle: &Handle,
        at: Position,
        buffer: Buffer<A>,
        chain: Chain,
    ) -> Result<Pending, Refused<A>>
    {
        self.stage(at, chain, Operation::Read {
            handle: handle.clone(),
            buffer,
        })
    }

    /// Append `buffer` to `segment` at its end, and move the end past it.
    /// The completion gives the buffer back with the position it wrote at.
    ///
    /// # Specification
    /// - ensures: on `Ok`, the pending key of the write at the segment's old
    ///   end, and the end moved past the buffer's length; on `Err`, the end
    ///   stays.
    /// - fails: [`Refused`], with the buffer, as [`Io::stage`] states.
    /// - panics: none.
    /// - executable: none — the write is the kernel's.
    ///
    /// # Errors
    /// [`Refused`] with the buffer, when the caller holds as many unread
    /// completions as the `Io` keeps, or the kernel refuses a submission.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two appends write at the start and past the first
    ///   buffer, and the end stands past both.
    /// - witness: `tests::io::an_append_owns_the_end_of_its_segment`
    #[inline]
    pub fn append(
        &mut self,
        segment: &mut Segment,
        buffer: Buffer<A>,
        chain: Chain,
    ) -> Result<Pending, Refused<A>>
    {
        let at = segment.end;
        let length = buffer.length();
        let pending = self.stage(at, chain, Operation::Write {
            handle: segment.handle.clone(),
            buffer,
        })?;
        segment.end = at.plus(length);
        Ok(pending)
    }

    /// Sync `segment`'s data, as `fdatasync(2)` does.
    ///
    /// # Specification
    /// - ensures: on `Ok`, the pending key of the sync, staged after each
    ///   submission before it.
    /// - fails: [`Refused`], as [`Io::stage`] states.
    /// - panics: none.
    /// - executable: none — the sync is the kernel's.
    ///
    /// # Errors
    /// [`Refused`] when the caller holds as many unread completions as the
    /// `Io` keeps, or the kernel refuses a submission.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a sync linked after a failed write completes
    ///   cancelled.
    /// - witness: `tests::io::a_failed_write_cancels_its_linked_sync`
    #[inline]
    pub fn sync(
        &mut self,
        segment: &Segment,
        chain: Chain,
    ) -> Result<Pending, Refused<A>>
    {
        self.stage(Position::from(0_u64), chain, Operation::Sync {
            handle: segment.handle.clone(),
        })
    }

    /// Cancel the submission `target`. Two completions answer: the
    /// target's, cancelled unless it ran, and the cancel's own, in either
    /// order.
    ///
    /// # Specification
    /// - ensures: on `Ok`, the pending key of the cancel. A target that no form
    ///   holds yet completes cancelled at once, with each submission linked
    ///   after it, and the cancel completes with 0. A target that a form holds
    ///   is cancelled there: the cancel completes with 0, or with
    ///   [`Errno::ALREADY`] or [`Errno::NO_ENTRY`] when the target runs or has
    ///   completed.
    /// - fails: [`Refused`] when the completions would pass what the `Io`
    ///   keeps, or the kernel refuses a submission.
    /// - panics: none.
    /// - executable: none — the target is the kernel's or the thread's.
    ///
    /// # Errors
    /// [`Refused`] when the caller holds too many unread completions, or the
    /// kernel refuses a submission.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a cancel of a staged write completes the write
    ///   cancelled with its buffer, and a cancel of a completed write finds no
    ///   entry.
    /// - witness: `tests::io::a_cancel_before_submission_completes_the_target_cancelled`
    /// - witness: `tests::io::a_cancel_after_completion_finds_no_entry`
    #[inline]
    pub fn cancel(
        &mut self,
        target: Pending,
    ) -> Result<Pending, Refused<A>>
    {
        let unread_limit = self.depth.saturating_mul(2);
        if let Some(index) = self.staged.iter().position(|order| order.key == target.0) {
            let run = self
                .staged
                .get(index ..)
                .and_then(|rest| rest.iter().position(|order| order.chain == Chain::Alone))
                .map_or_else(
                    || self.staged.len().saturating_sub(index),
                    |last| last.saturating_add(1),
                );
            if self.unread.len().saturating_add(run).saturating_add(1) > unread_limit {
                return Err(Refused {
                    reason: Reason::Unread,
                    buffer: None,
                });
            }
            if let Some(before) = index
                .checked_sub(1)
                .and_then(|before| self.staged.get_mut(before))
            {
                before.chain = Chain::Alone;
            }
            let end = index.saturating_add(run);
            for order in self.staged.drain(index .. end) {
                self.unread.push_back(order.done(Err(Errno::CANCELLED)));
            }
            let key = self.key();
            self.unread.push_back(Done {
                pending: Pending(key),
                outcome: Ok(Moved::from(0)),
                at: Position::from(0_u64),
                buffer: None,
            });
            return Ok(Pending(key));
        }
        match self.engine {
            Engine::Ring(_) => self.stage(Position::from(0_u64), Chain::Alone, Operation::Cancel {
                target: target.0,
            }),
            Engine::Blocking(_) => {
                if self.unread.len() >= unread_limit {
                    return Err(Refused {
                        reason: Reason::Unread,
                        buffer: None,
                    });
                }
                // The blocking form runs each order when the `Io` submits it,
                // so a target that no stage holds has completed.
                let outcome = Err(Errno::NO_ENTRY);
                let key = self.key();
                self.unread.push_back(Done {
                    pending: Pending(key),
                    outcome,
                    at: Position::from(0_u64),
                    buffer: None,
                });
                Ok(Pending(key))
            },
        }
    }

    /// Hand each staged submission to the form, which starts it.
    ///
    /// # Specification
    /// - ensures: on `Ok`, no submission stays staged; a chain ends here.
    /// - fails: the kernel's error number; a submission it did not take stays
    ///   staged.
    /// - panics: none.
    /// - executable: none — the queue is shared with the kernel.
    ///
    /// # Errors
    /// The kernel's error number from the submission.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a write submitted before the `Io` drops lands in its
    ///   file.
    /// - witness: `tests::io::dropping_an_io_completes_its_submitted_writes`
    #[inline]
    pub fn submit(&mut self) -> Result<(), Errno>
    {
        if let Some(last) = self.staged.last_mut() {
            last.chain = Chain::Alone;
        }
        let before = self.staged.len();
        let submitted = self.engine.flush(&mut self.staged);
        self.flushed = self
            .flushed
            .saturating_add(before.saturating_sub(self.staged.len()));
        submitted
    }

    /// The next completion: one the caller has not taken, or the next that
    /// the form gives, parked until it stands. `None` when the `Io` holds no
    /// submission.
    ///
    /// # Specification
    /// - ensures: on `Ok(Some)`, one completion that the caller has not taken
    ///   before; each submission completes once; `Ok(None)` when the `Io` holds
    ///   no submission and no completion.
    /// - fails: the kernel's error number.
    /// - panics: none.
    /// - executable: none — the completions are the kernel's or the thread's.
    ///
    /// # Errors
    /// The kernel's error number from the submission or the wait.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — three linked submissions give three completions in
    ///   order, and then none.
    /// - witness: `tests::io::a_linked_write_sync_and_read_complete_in_order`
    #[inline]
    pub fn wait(&mut self) -> Result<Option<Done<A>>, Errno>
    {
        if let Some(done) = self.unread.pop_front() {
            return Ok(Some(done));
        }
        self.submit()?;
        if self.flushed == 0 {
            return Ok(None);
        }
        let done = self.engine.wait()?;
        self.flushed = self.flushed.saturating_sub(1);
        Ok(Some(done))
    }

    /// Stage `operation` at `at`, after parking a full `Io` until a
    /// submission completes.
    ///
    /// # Specification
    /// - ensures: on `Ok`, the pending key of the staged submission; at most
    ///   `depth` submissions stand in flight, staged ones counted.
    /// - fails: [`Reason::Unread`] when the caller holds as many unread
    ///   completions as the `Io` keeps; [`Reason::Kernel`] when the kernel
    ///   refuses the submission of the staged entries. Either gives the buffer
    ///   back.
    /// - panics: none.
    /// - executable: none — the park is the kernel's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a full `Io` parks until a write completes, and gives
    ///   a buffer back when the caller reads no completion.
    /// - witness: `tests::io::a_full_io_parks_and_gives_back_what_it_cannot_hold`
    fn stage(
        &mut self,
        at: Position,
        chain: Chain,
        operation: Operation<A>,
    ) -> Result<Pending, Refused<A>>
    {
        if self.staged.len().saturating_add(self.flushed) >= self.depth
            && let Err(reason) = self.park()
        {
            return Err(Refused {
                reason,
                buffer: operation.into_buffer(),
            });
        }
        let key = self.key();
        let fault = self.faults.as_mut().and_then(|faults| match operation {
            Operation::Write { ref buffer, .. } => faults.write(Pending(key), buffer.length(), at),
            Operation::Read { ref buffer, .. } => faults.read(Pending(key), buffer.length()),
            Operation::Sync { .. } | Operation::Cancel { .. } => None,
        });
        let order = Order {
            key,
            at,
            chain,
            fate: Fate::Run,
            operation,
            fault,
        };
        if fault == Some(Injected::Lost) {
            let asked = order.operation.asked();
            self.unread.push_back(order.done(Ok(asked)));
        }
        else {
            self.staged.push(order);
        }
        Ok(Pending(key))
    }

    /// Submit what is staged, and park until one submission completes; then
    /// take each completion that stands, up to what the `Io` keeps.
    ///
    /// # Specification
    /// - ensures: on `Ok`, fewer than `depth` submissions stand in flight.
    /// - fails: [`Reason::Unread`] when the caller holds `depth` unread
    ///   completions; [`Reason::Kernel`] for the kernel's error.
    /// - panics: none.
    /// - executable: none — the park is the kernel's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a full `Io` parks until a write completes, and never
    ///   spins.
    /// - witness: `tests::io::a_full_io_parks_and_gives_back_what_it_cannot_hold`
    fn park(&mut self) -> Result<(), Reason>
    {
        self.submit().map_err(Reason::Kernel)?;
        if self.unread.len() >= self.depth {
            return Err(Reason::Unread);
        }
        if self.staged.len().saturating_add(self.flushed) < self.depth {
            return Ok(());
        }
        let done = self.engine.wait().map_err(Reason::Kernel)?;
        self.flushed = self.flushed.saturating_sub(1);
        self.unread.push_back(done);
        while self.unread.len() < self.depth {
            let Some(next) = self.engine.take()
            else {
                break;
            };
            self.flushed = self.flushed.saturating_sub(1);
            self.unread.push_back(next);
        }
        Ok(())
    }

    /// A fresh key: no two submissions of one `Io` share one.
    ///
    /// # Specification
    /// trivial.
    fn key(&mut self) -> Key
    {
        let key = Key::from(self.next);
        self.next = self.next.wrapping_add(1);
        key
    }
}

#[cfg(test)]
mod tests
{
    use super::Count;
    use super::Pinned;

    /// 8 MiB of room, the riscv64 host's limit, fits 32 buffers of 256 KiB
    /// and not 33; with 4 MiB held it fits 16; past the limit it fits none;
    /// with no limit it fits each buffer asked for.
    #[test]
    fn a_reservation_fits_within_the_limit()
    {
        let limit = Pinned(8 << 20_u32);
        let each = Pinned(256 << 10_u32);
        let fit =
            |held, count| u32::from(Pinned::fit(limit, Pinned(held), Count::from(count), each));
        assert_eq!(fit(0, 64), 32, "8 MiB holds 32 buffers of 256 KiB");
        assert_eq!(fit(0, 16), 16, "a smaller ask fits whole");
        assert_eq!(fit(4 << 20_u32, 64), 16, "the room past what is held");
        assert_eq!(fit(9 << 20_u32, 64), 0, "no room past the limit");
        assert_eq!(
            u32::from(Pinned::fit(
                Pinned(u64::MAX),
                Pinned(0),
                Count::from(64_u32),
                each
            )),
            64,
            "no limit fits each buffer"
        );
    }
}
