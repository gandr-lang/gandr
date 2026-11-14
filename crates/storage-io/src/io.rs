//! The interface: a buffer moves into each submission and comes back with
//! its completion, one completion for each submission, in the ring's form
//! or in the blocking form.

use alloc::collections::VecDeque;
use alloc::sync::Arc;
use std::fs::File;
use std::os::fd::AsFd as _;

use crate::blocking::Blocking;
use crate::buffer::Buffer;
use crate::record::Header;
use crate::record::Place;
use crate::ring::Count;
use crate::ring::Entry;
use crate::ring::Key;
use crate::ring::Moved;
use crate::ring::Position;
use crate::ring::Ring;
use crate::sys::Errno;

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
    /// Positioned calls on one thread that the [`Io`] owns.
    Blocking,
}

impl Form
{
    /// The form that a refusal of the ring's setup leaves: the blocking form
    /// for a refusal of permission, a kernel with no `io_uring_setup`, or a
    /// ring without stable submissions. Any other refusal is an error.
    ///
    /// # Specification
    /// - ensures: `Ok(Form::Blocking)` for [`Errno::PERMISSION`],
    ///   [`Errno::NO_SYSTEM_CALL`] and [`Errno::NOT_SUPPORTED`]; `Err(refusal)`
    ///   for any other.
    /// - panics: none.
    /// - executable: none — the predicate repeats the body's three comparisons.
    ///
    /// # Errors
    /// The refusal itself, when it is none of the three.
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
        {
            Ok(Self::Blocking)
        }
        else {
            Err(refusal)
        }
    }
}

/// A file that an [`Io`] reads and writes. Each submission holds a share of
/// it until its completion, so the descriptor stays open while the kernel
/// or the thread uses it.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Debug)]
pub struct Handle(Arc<File>);

impl From<File> for Handle
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(file: File) -> Self
    {
        Self(Arc::new(file))
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
        &self.0
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
#[derive(Debug)]
pub struct Done
{
    /// The submission that completes.
    pub pending: Pending,
    /// The bytes moved, or the error number.
    pub outcome: Result<Moved, Errno>,
    /// The position read or written at: for an append, the position it
    /// wrote at.
    pub at: Position,
    /// The buffer that the submission took, for a read or a write.
    pub buffer: Option<Buffer>,
}

/// Why the [`Io`] refuses a submission.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Reason
{
    /// The caller holds as many completions unread as the [`Io`] keeps: it
    /// takes one with [`Io::wait`] before it submits again.
    Unread,
    /// The kernel refused the submission of the staged entries.
    Kernel(Errno),
}

/// A refused submission, with the buffer it would have taken.
///
/// # Specification
/// trivial.
#[derive(Debug)]
pub struct Refused
{
    /// Why the [`Io`] refuses it.
    pub reason: Reason,
    /// The buffer, given back.
    pub buffer: Option<Buffer>,
}

/// What a submission does, with what it holds until its completion.
///
/// # Specification
/// trivial.
#[derive(Debug)]
pub enum Operation
{
    /// A read into `buffer` from the handle's file. With `expect`, its
    /// completion checks the header at the start of the bytes read.
    Read
    {
        /// The file.
        handle: Handle,
        /// The bytes to read into.
        buffer: Buffer,
        /// The place whose record the read expects, if it expects one.
        expect: Option<Place>,
    },
    /// A write of `buffer` into the handle's file.
    Write
    {
        /// The file.
        handle: Handle,
        /// The bytes to write.
        buffer: Buffer,
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

impl Operation
{
    /// The buffer that the operation holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_buffer(self) -> Option<Buffer>
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

    /// The outcome of the operation once it moved `moved` bytes: a read
    /// that expects a place checks the header that it read.
    ///
    /// # Specification
    /// - ensures: `Ok(moved)` for each operation but a read that expects a
    ///   place; for that read, `Ok(moved)` only when it read a whole header
    ///   whose checksum holds and which names the place.
    /// - fails: [`Errno::CORRUPT`] for a short read or a header that
    ///   [`Buffer::header`] refuses.
    /// - panics: none.
    /// - executable: none — the read's bytes are the kernel's.
    ///
    /// # Errors
    /// [`Errno::CORRUPT`] for a short read or a header of another place.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a read of a record at its own place completes with
    ///   its bytes, and a read of a misdirected or changed record completes
    ///   corrupt.
    /// - witness: `tests::record::a_read_of_the_expected_place_passes`
    /// - witness: `tests::record::a_misdirected_record_reads_corrupt`
    fn checked(
        &self,
        moved: Moved,
    ) -> Result<Moved, Errno>
    {
        match *self {
            Self::Read {
                ref buffer,
                expect: Some(place),
                ..
            } => {
                if moved < Header::size() {
                    Err(Errno::CORRUPT)
                }
                else {
                    buffer.header(place).map(|_header| moved)
                }
            },
            Self::Read { expect: None, .. }
            | Self::Write { .. }
            | Self::Sync { .. }
            | Self::Cancel { .. } => Ok(moved),
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
pub struct Order
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
    pub operation: Operation,
}

impl Order
{
    /// The completion of this order with `outcome`, which gives its buffer
    /// back. A read that expects a place completes corrupt when its header
    /// fails the check.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn done(
        self,
        outcome: Result<Moved, Errno>,
    ) -> Done
    {
        let outcome = outcome.and_then(|moved| self.operation.checked(moved));
        Done {
            pending: Pending(self.key),
            outcome,
            at: self.at,
            buffer: self.operation.into_buffer(),
        }
    }

    /// The ring's entry for this order, over the buffer that the order
    /// holds.
    ///
    /// # Specification
    /// trivial.
    fn entry(&mut self) -> Entry
    {
        let entry = match self.operation {
            Operation::Read {
                ref handle,
                ref mut buffer,
                ..
            } => Entry::read(handle.0.as_fd(), buffer, self.at, self.key),
            Operation::Write {
                ref handle,
                ref buffer,
            } => Entry::write(handle.0.as_fd(), buffer, self.at, self.key),
            Operation::Sync { ref handle } => Entry::sync(handle.0.as_fd(), self.key),
            Operation::Cancel { target } => Entry::cancel(target, self.key),
        };
        match self.chain {
            Chain::Alone => entry,
            Chain::Linked => entry.linked(),
        }
    }
}

/// The ring's form: the ring, and the orders that the kernel holds, each
/// with its buffer and its file until its completion.
struct Uring
{
    /// The ring.
    ring: Ring,
    /// The orders that the kernel holds.
    flight: Vec<Order>,
}

impl Uring
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
        staged: &mut Vec<Order>,
    ) -> Result<(), Errno>
    {
        let mut pushed = 0_usize;
        for order in staged.iter_mut() {
            let entry = order.entry();
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
    fn take(&mut self) -> Option<Done>
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
    fn wait(&mut self) -> Result<Done, Errno>
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

impl Drop for Uring
{
    /// Wait for each order that the kernel holds, so the kernel writes into
    /// no buffer after it is freed. A ring that the kernel stops answering
    /// leaks the buffers it holds.
    ///
    /// # Specification
    /// trivial.
    fn drop(&mut self)
    {
        while !self.flight.is_empty() {
            if self.take().is_some() {
                continue;
            }
            match self.ring.submit(Count::from(1_u32)) {
                Ok(_consumed) => {},
                Err(errno) if errno == Errno::INTERRUPTED => {},
                Err(_errno) => {
                    let _leaked: &mut [Order] = core::mem::take(&mut self.flight).leak();
                    return;
                },
            }
        }
    }
}

/// The form that an [`Io`] runs, with its state.
enum Engine
{
    /// The kernel's `io_uring`.
    Ring(Uring),
    /// One thread of positioned calls.
    Blocking(Blocking),
}

impl Engine
{
    /// Hand each staged order to the form.
    ///
    /// # Specification
    /// trivial.
    fn flush(
        &mut self,
        staged: &mut Vec<Order>,
    ) -> Result<(), Errno>
    {
        match *self {
            Self::Ring(ref mut uring) => uring.flush(staged),
            Self::Blocking(ref blocking) => {
                blocking.flush(staged);
                Ok(())
            },
        }
    }

    /// The next completion, parked until one stands.
    ///
    /// # Specification
    /// trivial.
    fn wait(&mut self) -> Result<Done, Errno>
    {
        match *self {
            Self::Ring(ref mut uring) => uring.wait(),
            Self::Blocking(ref blocking) => blocking.wait(),
        }
    }

    /// The next completion that stands, if one does.
    ///
    /// # Specification
    /// trivial.
    fn take(&mut self) -> Option<Done>
    {
        match *self {
            Self::Ring(ref mut uring) => uring.take(),
            Self::Blocking(ref blocking) => blocking.take(),
        }
    }
}

/// One worker's IO.
///
/// It holds at most `depth` submissions in flight, and at most `2 × depth`
/// completions that the caller has not taken. A buffer moves into each
/// submission and comes back with its completion.
pub struct Io
{
    /// The form, with its state.
    engine: Engine,
    /// The most submissions in flight, staged ones counted.
    depth: usize,
    /// The submissions that no form holds yet.
    staged: Vec<Order>,
    /// The submissions that the form holds, without their completions.
    flushed: usize,
    /// The completions that the caller has not taken.
    unread: VecDeque<Done>,
    /// The key of the next submission.
    next: u64,
}

impl Io
{
    /// An `Io` of `depth` submissions in flight, in the ring's form where
    /// the kernel gives a ring, and in the blocking form where it refuses
    /// one as [`Form::after`] reads the refusal.
    ///
    /// # Specification
    /// - ensures: on `Ok`, an `Io` that holds nothing, whose form is the ring's
    ///   when the kernel set one up.
    /// - fails: [`Errno::INVALID`] for a depth of zero; a refusal of the ring
    ///   that [`Form::after`] reads as an error; the error of the blocking
    ///   form's thread.
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
    /// - fails: [`Errno::INVALID`] for a depth of zero; the error of the
    ///   thread's spawn.
    /// - panics: none.
    /// - executable: none — the thread is the system's.
    ///
    /// # Errors
    /// [`Errno::INVALID`] for a depth of zero, and the error number of a
    /// thread that does not spawn.
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
        Ok(Self::with(Engine::Blocking(Blocking::new(depth)?), depth))
    }

    /// An `Io` over `engine` that holds nothing.
    ///
    /// # Specification
    /// trivial.
    fn with(
        engine: Engine,
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
        buffer: Buffer,
        chain: Chain,
    ) -> Result<Pending, Refused>
    {
        self.stage(at, chain, Operation::Read {
            handle: handle.clone(),
            buffer,
            expect: None,
        })
    }

    /// Read the record that `expected` places, from `handle` at its offset
    /// into `buffer`, which comes back with the completion. The completion
    /// checks the record's header before the bytes become a value.
    ///
    /// # Specification
    /// - ensures: on `Ok`, the pending key of the read, staged after each
    ///   submission before it; its completion is [`Errno::CORRUPT`] unless it
    ///   read a whole header that holds and names `expected`.
    /// - fails: [`Refused`], with the buffer, as [`Io::stage`] states.
    /// - panics: none.
    /// - executable: none — the read is the kernel's.
    ///
    /// # Errors
    /// [`Refused`] with the buffer, when the caller holds as many unread
    /// completions as the `Io` keeps, or the kernel refuses a submission.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a read of a record at its own place completes with
    ///   its bytes, and a read of a misdirected or changed record completes
    ///   corrupt, under both forms.
    /// - witness: `tests::record::a_read_of_the_expected_place_passes`
    /// - witness: `tests::record::a_misdirected_record_reads_corrupt`
    #[inline]
    pub fn read_record(
        &mut self,
        handle: &Handle,
        expected: Place,
        buffer: Buffer,
        chain: Chain,
    ) -> Result<Pending, Refused>
    {
        self.stage(expected.offset, chain, Operation::Read {
            handle: handle.clone(),
            buffer,
            expect: Some(expected),
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
        buffer: Buffer,
        chain: Chain,
    ) -> Result<Pending, Refused>
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

    /// Sync `segment`'s data and metadata.
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
    ) -> Result<Pending, Refused>
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
    ) -> Result<Pending, Refused>
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
            Engine::Blocking(ref blocking) => {
                if self.unread.len() >= unread_limit {
                    return Err(Refused {
                        reason: Reason::Unread,
                        buffer: None,
                    });
                }
                let outcome = blocking.cancel(target.0);
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
    pub fn wait(&mut self) -> Result<Option<Done>, Errno>
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
        operation: Operation,
    ) -> Result<Pending, Refused>
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
        self.staged.push(Order {
            key,
            at,
            chain,
            fate: Fate::Run,
            operation,
        });
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
