//! The ring's adapter: each member of the operation set goes through the
//! kernel's io_uring, the timer by its timeout and a cancel by its
//! asynchronous cancel, and the linked pair as two entries under the ring's
//! link flag in one submission.

use ::alloc::boxed::Box;
use ::alloc::vec;
use ::gandr_runtime_uring::IoUring;
use ::gandr_runtime_uring::SlotDesc;
use ::gandr_runtime_uring::arg::Count;
use ::gandr_runtime_uring::arg::Fd;
use ::gandr_runtime_uring::arg::Flags;
use ::gandr_runtime_uring::arg::Len;
use ::gandr_runtime_uring::arg::Offset;
use ::gandr_runtime_uring::arg::UserData;
use ::rustix::io::Errno;

use crate::adapter::Adapter;
use crate::completion::Cqe;
use crate::error::RuntimeError;
use crate::op::Descriptor;
use crate::op::Lent;
use crate::op::Op;
use crate::op::Ticket;
use crate::submission::Depth;
use crate::submission::Key;
use crate::submission::Lookup;
use crate::submission::Table;

/// The bit of the user data that marks a cancel's own completion. The other
/// bits name the slot of the operation that the cancel ends, so a refused
/// cancel names its operation. A key of the table is below the ring's depth,
/// so no request's user data holds the bit.
const CANCEL: u64 = 1 << 63;

/// The bit of the user data that marks the write of a linked pair: the
/// pair's sync carries the slot's user data alone.
const HEAD: u64 = 1 << 62;

/// The offset that tells the kernel to read or write at the file's own
/// position, as a pipe or a socket takes.
const AT_POSITION: u64 = u64::MAX;

/// What the ring's completion of a slot needs beyond its result: whether the
/// slot holds a timer, whose expiry the ring posts as `ETIME`, or a linked
/// pair, which completes once after both of its entries.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Slot
{
    /// The slot's completion is its operation's result.
    Plain,
    /// The slot holds a timer: its expiry is a success.
    Timer,
    /// The ring holds both entries of the slot's pair.
    Linked,
    /// The pair's write completed with this result; the sync's completion
    /// follows.
    Wrote(i32),
    /// The pair's sync completed with this result; the write's completion
    /// follows.
    Synced(i32),
}

/// The ring's adapter: the kernel's ring, and the state of each slot.
#[non_exhaustive]
pub struct Uring
{
    /// The kernel's ring.
    io: IoUring<'static>,
    /// For each slot, what its completion needs beyond its result.
    slots: Box<[Slot]>,
}

/// The pair's one result from the write's result and the sync's: the first
/// refusal, or the write's count.
///
/// # Specification
///
/// - provides: the write's result when it is a refusal or when the sync
///   succeeds, and the sync's refusal otherwise.
/// - panics: none.
/// - executable: none — the results are the kernel's.
///
/// # Adequacy
///
/// - hypothesis: L3 — a pair's write of four bytes and its sync complete as one
///   count of four.
/// - witness: `io::fd::test::write_sync`
const fn joined(
    wrote: i32,
    synced: i32,
) -> Cqe
{
    if wrote < 0 || synced >= 0 {
        Cqe::new(wrote)
    }
    else {
        Cqe::new(synced)
    }
}

/// Records the completion of one entry of the pair in `slot`, and gives the
/// pair's one completion once both of its entries have completed.
///
/// # Specification
///
/// - provides: the pair's completion once both of its entries have completed,
///   and nothing before.
/// - fails: `Unknown` with the user data when the slot holds no pair, or holds
///   the posted entry's result already.
/// - panics: none.
/// - executable: none — the results are the kernel's.
///
/// # Adequacy
///
/// - hypothesis: L3 — a pair completes once, after both of its entries.
/// - witness: `io::fd::test::write_sync`
/// - witness: `io::fd::test::write_sync_in_flight`
fn pair_step(
    slot: &mut Slot,
    data: u64,
    res: i32,
) -> Result<Option<Cqe>, RuntimeError>
{
    let head = data & HEAD != 0;
    let (next, done) = match (*slot, head) {
        (Slot::Linked, true) => (Slot::Wrote(res), None),
        (Slot::Linked, false) => (Slot::Synced(res), None),
        (Slot::Synced(synced), true) => (Slot::Plain, Some(joined(res, synced))),
        (Slot::Wrote(wrote), false) => (Slot::Plain, Some(joined(wrote, res))),
        (Slot::Plain | Slot::Timer | Slot::Wrote(_) | Slot::Synced(_), _) => {
            return Err(RuntimeError::Unknown(data));
        },
    };
    *slot = next;
    Ok(done)
}

/// Records one completion of the ring: a cancel's own, an entry of a pair,
/// or an operation's.
///
/// # Specification
///
/// - ensures: an operation's completion, and a pair's once both entries
///   complete, is in its slot.
/// - fails: `Cancel` with the slot when a cancel fails other than with `ENOENT`
///   or `EALREADY`, and `Unknown` when the user data names no slot.
/// - panics: none.
/// - executable: none — the results are the kernel's.
///
/// # Adequacy
///
/// - hypothesis: L3 — each member's test records its completion.
/// - witness: `io::fd::test::echo`
/// - witness: `io::fd::test::timer`
/// - witness: `io::fd::test::write_sync`
fn record(
    slots: &mut [Slot],
    table: &Table,
    data: u64,
    cqe: Cqe,
) -> Result<(), RuntimeError>
{
    if data & CANCEL != 0 {
        // A cancel finds its operation, or finds it already complete or past
        // the point of a cancel; the operation's own completion follows in
        // each case. Any other refusal names the operation's slot.
        return match cqe.done() {
            Ok(()) | Err(RuntimeError::Kernel(Errno::NOENT | Errno::ALREADY)) => Ok(()),
            Err(RuntimeError::Kernel(errno)) => Err(RuntimeError::Cancel {
                data: data & !(CANCEL | HEAD),
                errno,
            }),
            Err(error) => Err(error),
        };
    }
    let key = Key::try_from(data & !HEAD).map_err(|_overflow| RuntimeError::Unknown(data))?;
    let slot = slots
        .get_mut(usize::from(key))
        .ok_or(RuntimeError::Unknown(data))?;
    let cqe = match *slot {
        Slot::Plain => cqe,
        Slot::Timer => {
            *slot = Slot::Plain;
            // The ring posts a timer's expiry as `ETIME`: the contract's
            // timer completes with no refusal when its span passes.
            if cqe.done() == Err(RuntimeError::Kernel(Errno::TIME)) {
                Cqe::new(0)
            }
            else {
                cqe
            }
        },
        Slot::Linked | Slot::Wrote(_) | Slot::Synced(_) => {
            let Some(cqe) = pair_step(slot, data, cqe.res())?
            else {
                return Ok(());
            };
            cqe
        },
    };
    if table.complete(key, cqe) == Lookup::Missing {
        return Err(RuntimeError::Unknown(data));
    }
    Ok(())
}

/// The socket that `fd` names, borrowed while its operation is prepared.
///
/// # Safety
///
/// - unsafe invariants: `fd` is an open descriptor that the operation borrows
///   until its completion.
///
/// # Specification
///
/// trivial.
unsafe fn socket_of(fd: Descriptor) -> ::std::mem::ManuallyDrop<::socket2::Socket>
{
    // SAFETY: the caller's invariant; the socket is never dropped, so the
    // descriptor stays its owner's.
    let socket = unsafe { <::socket2::Socket as ::std::os::fd::FromRawFd>::from_raw_fd(fd.into()) };
    ::std::mem::ManuallyDrop::new(socket)
}

impl Uring
{
    /// Prepares one entry for `op` with `data`, when the queue has room.
    ///
    /// # Specification
    ///
    /// - requires: each memory that `op` lends outlives its completion.
    /// - ensures: on success, the queue holds the entry with `data`.
    /// - fails: `Full` when the queue has no room, `Overrun` when a length
    ///   passes the ring's width, and `Unsupported` for the linked pair, which
    ///   takes two entries.
    /// - panics: none.
    /// - executable: none — the entry is the kernel's memory.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — each member's test completes through its entry.
    /// - witness: `io::fd::test::echo`
    /// - witness: `io::fd::test::timer`
    /// - witness: `io::fd::test::cancel`
    fn one(
        &mut self,
        data: u64,
        op: Op<'_>,
    ) -> Result<(), RuntimeError>
    {
        let mut sq = self.io.squeue();
        let mut sqe = sq.get_sqe().ok_or(RuntimeError::Full)?;
        match op {
            Op::Nop => {
                // SAFETY: a no-op reads no pointer and names no descriptor.
                unsafe {
                    sqe.prep_nop();
                }
            },
            Op::Read { fd, into } => {
                let len = u32::try_from(usize::from(into.len()))
                    .map_err(|_overflow| RuntimeError::Overrun)?;
                // SAFETY: the bytes are lent for the scope's life, and the
                // scope's end drains the read before the borrow ends.
                unsafe {
                    sqe.prep_read(
                        Fd(fd.into()),
                        into.ptr().as_ptr().cast(),
                        Len(len),
                        Offset(AT_POSITION),
                    );
                }
            },
            Op::Write { fd, from } => {
                let len = u32::try_from(usize::from(from.len()))
                    .map_err(|_overflow| RuntimeError::Overrun)?;
                // SAFETY: the bytes are lent for the scope's life, and the
                // scope's end drains the write before the borrow ends.
                unsafe {
                    sqe.prep_write(
                        Fd(fd.into()),
                        from.ptr().as_ptr().cast_const().cast(),
                        Len(len),
                        Offset(AT_POSITION),
                    );
                }
            },
            Op::Accept {
                fd,
                mut peer,
                mut len,
                ..
            } => {
                let flags = ::rustix::net::SocketFlags::empty();
                // SAFETY: the operation borrows the descriptor until its
                // completion.
                let socket = unsafe { socket_of(fd) };
                // SAFETY: the peer's storage and its length are lent for the
                // scope's life, and the scope's end drains the accept before
                // the borrow ends.
                unsafe {
                    sqe.prep_accept(
                        SlotDesc::Desc(&*socket),
                        peer.as_mut(),
                        Len(len.as_mut()),
                        flags,
                        None,
                    );
                }
            },
            Op::Timer { after } => {
                // SAFETY: the span is lent for the scope's life, the ring
                // reads it when it takes the entry, before the scope's end,
                // and its layout is the kernel's time.
                unsafe {
                    sqe.prep_timeout(::core::ptr::from_ref(after).cast(), Count(0), Flags(0));
                }
            },
            Op::Cancel { target } => {
                let target = u64::try_from(target.0).map_err(|_overflow| RuntimeError::Full)?;
                // SAFETY: a cancel by user data reads no pointer and names no
                // descriptor.
                unsafe {
                    sqe.prep_cancel64(UserData(target), Flags(0_i32));
                }
            },
            Op::Socket {
                domain,
                ty,
                protocol,
            } => {
                let flags = ::rustix::net::SocketFlags::empty();
                // SAFETY: a socket's creation reads no pointer and names no
                // descriptor.
                unsafe {
                    sqe.prep_socket(domain, ty, protocol, flags, None);
                }
            },
            Op::Bind { fd, addr } => {
                // SAFETY: the operation borrows the descriptor until its
                // completion.
                let socket = unsafe { socket_of(fd) };
                // SAFETY: the address is lent for the scope's life, and the
                // scope's end drains the bind before the borrow ends.
                unsafe {
                    sqe.prep_bind(SlotDesc::Desc(&*socket), addr);
                }
            },
            Op::Listen { fd, backlog } => {
                // SAFETY: the operation borrows the descriptor until its
                // completion.
                let socket = unsafe { socket_of(fd) };
                // SAFETY: a listen reads no pointer of the caller's.
                unsafe {
                    sqe.prep_listen(SlotDesc::Desc(&*socket), Count(backlog.into()));
                }
            },
            Op::Recv { fd, into } => {
                // SAFETY: the bytes are lent for the scope's life, and the
                // scope's end drains the receive before the borrow ends.
                unsafe {
                    sqe.prep_recv(
                        Fd(fd.into()),
                        into.ptr().as_ptr().cast(),
                        Len(usize::from(into.len())),
                        Flags(0_i32),
                    );
                }
            },
            Op::WriteSync { .. } => return Err(RuntimeError::Unsupported(op.member())),
        }
        // SAFETY: the user data is a number that the kernel only hands back.
        unsafe {
            sqe.set_data64(UserData(data));
        }
        Ok(())
    }

    /// Prepares the linked pair: a write of `from` to `fd` under the ring's
    /// link flag, then the sync of `fd`, both in one run of the queue.
    ///
    /// # Specification
    ///
    /// - requires: the bytes outlive the pair's completion.
    /// - ensures: on success, the queue holds both entries and the slot's pair
    ///   stands linked.
    /// - fails: `Full` when the queue has no room for both, `Overrun` when the
    ///   length passes the ring's width, and `Unknown` for a slot past the
    ///   table.
    /// - panics: none.
    /// - executable: none — the entries are the kernel's memory.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — a pair's sync completes after its write, and the file
    ///   holds the bytes.
    /// - witness: `io::fd::test::write_sync`
    fn pair(
        &mut self,
        key: Key,
        data: u64,
        fd: Descriptor,
        from: Lent<'_>,
    ) -> Result<(), RuntimeError>
    {
        let len =
            u32::try_from(usize::from(from.len())).map_err(|_overflow| RuntimeError::Overrun)?;
        let Self {
            ref mut io,
            ref mut slots,
        } = *self;
        let slot = slots
            .get_mut(usize::from(key))
            .ok_or(RuntimeError::Unknown(data))?;
        let mut sq = io.squeue();
        let mut run = sq.get_sqes(Count(2)).ok_or(RuntimeError::Full)?;
        let (Some(mut write), Some(mut sync)) = (run.next(), run.next())
        else {
            return Err(RuntimeError::Full);
        };
        // SAFETY: the bytes are lent for the scope's life, and the scope's
        // end drains the pair before the borrow ends; the link flag is the
        // kernel's own.
        unsafe {
            write.prep_write(
                Fd(fd.into()),
                from.ptr().as_ptr().cast_const().cast(),
                Len(len),
                Offset(AT_POSITION),
            );
            write.set_flags(Flags(::gandr_runtime_uring::sqe::IO_LINK));
            write.set_data64(UserData(data | HEAD));
        }
        // SAFETY: a sync names the descriptor that the pair borrows, and reads
        // no pointer.
        unsafe {
            sync.prep_fsync(Fd(fd.into()), Flags(0));
            sync.set_data64(UserData(data));
        }
        *slot = Slot::Linked;
        Ok(())
    }

    /// Prepares the cancel of the user data `target`, its own completion
    /// marked as a cancel's, flushing the queue once when it has no room.
    ///
    /// # Specification
    ///
    /// - ensures: on success, the queue holds the cancel.
    /// - fails: `Full` when the queue has no room after a flush, and the
    ///   kernel's refusal of the flush.
    /// - panics: none.
    /// - executable: none — the entry is the kernel's memory.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — the scope's end cancels an accept and a receive that
    ///   the kernel holds.
    /// - witness: `io::socket::test::socket::accept_in_flight`
    /// - witness: `io::socket::test::socket::recv_in_flight`
    fn cancel_data(
        &mut self,
        target: u64,
    ) -> Result<(), RuntimeError>
    {
        let prep = |sqe: &mut ::gandr_runtime_uring::Sqe64<'_>| {
            // SAFETY: a cancel by user data reads no pointer and names no
            // descriptor.
            unsafe {
                sqe.prep_cancel64(UserData(target), Flags(0_i32));
            }
            // SAFETY: the user data is a number that the kernel only hands
            // back.
            unsafe {
                sqe.set_data64(UserData(CANCEL | target));
            }
        };
        let mut sq = self.io.squeue();
        // Each entry that the queue gives is prepared: the next submission
        // takes an entry that a call takes and leaves, unprepared.
        if let Some(mut sqe) = sq.get_sqe() {
            prep(&mut sqe);
            return Ok(());
        }
        sq.submit()?;
        let mut sqe = sq.get_sqe().ok_or(RuntimeError::Full)?;
        prep(&mut sqe);
        Ok(())
    }
}

impl Adapter for Uring
{
    /// A new ring of the kernel with `depth` entries.
    ///
    /// # Specification
    ///
    /// - provides: an adapter whose ring has `depth` entries, and no pair.
    /// - fails: the kernel's refusal of the ring.
    /// - panics: none.
    /// - executable: none — the ring is the kernel's.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — the kernel of the test host makes the ring.
    /// - witness: `runtime::test::new`
    ///
    /// # Errors
    ///
    /// The kernel's refusal of the ring.
    ///
    /// # Cost
    ///
    /// - allocation: the state of each slot, setup
    #[inline]
    fn open(depth: Depth) -> Result<Self, RuntimeError>
    {
        let entries = u32::try_from(usize::from(depth)).map_err(|_overflow| RuntimeError::Full)?;
        let io = IoUring::builder().entries(Count(entries)).build()?;
        let slots = vec![Slot::Plain; usize::from(depth)].into_boxed_slice();
        Ok(Self { io, slots })
    }

    /// Prepares `op`'s entries in the ring, which the next `wait` submits.
    ///
    /// # Specification
    ///
    /// - requires: each memory that `op` lends outlives its completion.
    /// - ensures: on success, the ring holds the operation's entries, whose
    ///   completions name the ticket's slot.
    /// - fails: `Full` when the queue has no room, and `Overrun` when a length
    ///   passes the ring's width.
    /// - panics: none.
    /// - executable: none — the entries are the kernel's memory.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — each member's test completes through the ring.
    /// - witness: `io::fd::test::echo`
    /// - witness: `io::fd::test::write_sync`
    ///
    /// # Errors
    ///
    /// As `fails` states.
    ///
    /// # Cost
    ///
    /// - allocation: none in steady state
    #[inline]
    fn submit(
        &mut self,
        ticket: Ticket,
        op: Op<'_>,
    ) -> Result<(), RuntimeError>
    {
        let data = u64::try_from(ticket.0).map_err(|_overflow| RuntimeError::Full)?;
        match op {
            Op::WriteSync { fd, from } => self.pair(ticket.0, data, fd, from),
            Op::Timer { .. } => {
                self.one(data, op)?;
                let slot = self
                    .slots
                    .get_mut(usize::from(ticket.0))
                    .ok_or(RuntimeError::Unknown(data))?;
                *slot = Slot::Timer;
                Ok(())
            },
            Op::Nop
            | Op::Read { .. }
            | Op::Write { .. }
            | Op::Accept { .. }
            | Op::Cancel { .. }
            | Op::Socket { .. }
            | Op::Bind { .. }
            | Op::Listen { .. }
            | Op::Recv { .. } => self.one(data, op),
        }
    }

    /// Cancels the operation of the ticket's slot by its user data, and the
    /// write of its pair when it holds one.
    ///
    /// # Specification
    ///
    /// - ensures: on success, the queue holds a cancel of each entry of the
    ///   slot's operation.
    /// - fails: `Full` when the queue has no room after a flush, and the
    ///   kernel's refusal of the flush.
    /// - panics: none.
    /// - executable: none — the entries are the kernel's memory.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — the scope's end drains an accept, a receive and a
    ///   pending read.
    /// - witness: `io::socket::test::socket::accept_in_flight`
    /// - witness: `io::fd::test::timer_in_flight`
    /// - witness: `io::fd::test::write_sync_in_flight`
    ///
    /// # Errors
    ///
    /// As `fails` states.
    #[inline]
    fn cancel(
        &mut self,
        ticket: Ticket,
    ) -> Result<(), RuntimeError>
    {
        let data = u64::try_from(ticket.0).map_err(|_overflow| RuntimeError::Full)?;
        let linked = self
            .slots
            .get(usize::from(ticket.0))
            .is_some_and(|slot| matches!(*slot, Slot::Linked | Slot::Wrote(_) | Slot::Synced(_)));
        if linked {
            self.cancel_data(data | HEAD)?;
        }
        self.cancel_data(data)
    }

    /// Submits the prepared entries, waits for at least one completion, and
    /// records each ready completion in its slot of `table`.
    ///
    /// # Specification
    ///
    /// - ensures: each completion that was ready is in its slot, and a pair's
    ///   slot completes once both of its entries have.
    /// - fails: the kernel's error when the submission or the wait fails;
    ///   `Cancel` with the operation's slot when a cancel fails other than with
    ///   `ENOENT` or `EALREADY`; `Unknown` when a completion names no slot.
    /// - panics: none.
    /// - executable: none — the kernel's state of the ring is not a value that
    ///   the call can read.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — a thousand no-ops each complete into their slots, and
    ///   the cancels of a scope's end complete with no refusal.
    /// - witness: `tests::path::request::a_request_allocates_nothing_after_the_start`
    /// - witness: `io::socket::test::socket::accept_in_flight`
    ///
    /// # Errors
    ///
    /// As `fails` states.
    ///
    /// # Cost
    ///
    /// - allocation: none in steady state
    #[inline]
    fn wait(
        &mut self,
        table: &Table,
    ) -> Result<(), RuntimeError>
    {
        let Self {
            ref mut io,
            ref mut slots,
        } = *self;
        let (mut squ, mut cqu) = io.queues();
        squ.submit_and_wait(Count(1))?;
        for cqe in cqu.ready() {
            let UserData(data) = cqe.user_data();
            record(slots, table, data, Cqe::from(cqe))?;
        }
        Ok(())
    }
}
