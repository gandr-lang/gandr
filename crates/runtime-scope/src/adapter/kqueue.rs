//! The kqueue adapter of macOS. A member that waits on a descriptor
//! registers the descriptor's readiness, one registration for each slot,
//! and does its call when the descriptor is ready. The call takes at most
//! the bytes that the readiness counts, so no call blocks the thread. A
//! timer is the kernel's timer filter, and a cancel deletes the
//! registration of its target. A member that does not wait, as the creation
//! of a socket, runs when the scope submits it, and the next `wait` records
//! its completion.
//!
//! The linked pair needs a thread of a pool for the sync of its file. This
//! adapter has no pool, so it refuses the pair by name.

use ::alloc::boxed::Box;
use ::alloc::vec;
use ::alloc::vec::Vec;
use ::core::ffi::c_int;
use ::core::ffi::c_void;
use ::core::ptr::NonNull;
use ::core::time::Duration;
use ::rustix::io::Errno;
use ::socket2::SockAddrStorage;
use ::socket2::socklen_t;
use ::std::os::fd::AsRawFd as _;
use ::std::os::fd::IntoRawFd as _;
use ::std::os::fd::OwnedFd;
use ::std::os::fd::RawFd;

use crate::adapter::Adapter;
use crate::adapter::socket_of;
use crate::completion::Cqe;
use crate::error::RuntimeError;
use crate::op::Op;
use crate::op::Ticket;
use crate::submission::Depth;
use crate::submission::Key;
use crate::submission::Lookup;
use crate::submission::Table;

/// The largest count that one call moves: a completion's result is an
/// `i32`.
const MOST: usize = 0x7fff_ffff;

/// What a slot waits for, and the call that its readiness starts.
#[derive(Clone, Copy, Debug)]
enum Wait
{
    /// The slot waits for nothing of this adapter.
    Idle,
    /// A read from `fd` into `len` bytes at `into`, once `fd` is readable.
    Read
    {
        /// The descriptor.
        fd: RawFd,
        /// The lent bytes.
        into: NonNull<u8>,
        /// Their count.
        len: usize,
    },
    /// A receive from `fd` into `len` bytes at `into`, once `fd` is readable.
    Recv
    {
        /// The socket.
        fd: RawFd,
        /// The lent bytes.
        into: NonNull<u8>,
        /// Their count.
        len: usize,
    },
    /// A write of `len` bytes at `from` to `fd`, once `fd` is writable.
    Write
    {
        /// The descriptor.
        fd: RawFd,
        /// The lent bytes.
        from: NonNull<u8>,
        /// Their count.
        len: usize,
    },
    /// An accept on the listening socket `fd`, once a connection waits.
    Accept
    {
        /// The listening socket.
        fd: RawFd,
        /// The lent storage of the peer's address.
        peer: NonNull<SockAddrStorage>,
        /// The lent length of the peer's address.
        len: NonNull<socklen_t>,
    },
    /// A timer of the kernel's timer filter.
    Timer,
}

/// The readiness that a call waits for.
#[derive(Clone, Copy, Debug)]
enum Ready
{
    /// The descriptor has bytes to read, or a connection to accept.
    Readable,
    /// The descriptor has room to write.
    Writable,
}

/// Whether a change adds a registration or deletes it.
#[derive(Clone, Copy, Debug)]
enum Change
{
    /// The change adds the registration, which fires once.
    Add,
    /// The change deletes the registration.
    Delete,
}

/// Whether the descriptor's far end is closed, as its readiness tells.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum End
{
    /// The far end is open.
    Open,
    /// The far end is closed: a read finds the end of the bytes.
    Closed,
}

impl Wait
{
    /// The descriptor and the readiness that the slot's call waits for.
    ///
    /// # Specification
    ///
    /// trivial.
    const fn readiness(self) -> Option<(RawFd, Ready)>
    {
        match self {
            Self::Read { fd, .. } | Self::Recv { fd, .. } | Self::Accept { fd, .. } => {
                Some((fd, Ready::Readable))
            },
            Self::Write { fd, .. } => Some((fd, Ready::Writable)),
            Self::Idle | Self::Timer => None,
        }
    }
}

/// The user data of the slot `key`: the key's number, not an address.
///
/// # Specification
///
/// trivial.
fn udata(key: Key) -> *mut c_void
{
    ::core::ptr::without_provenance_mut(usize::from(key))
}

/// The change of the readiness registration of `fd` for the slot `key`.
///
/// # Specification
///
/// - provides: the kernel's event that adds or deletes the registration of
///   `fd`'s readiness under the user data of `key`.
/// - fails: `Kernel(EBADF)` when `fd` is negative.
/// - panics: none.
/// - executable: none — the event is the kernel's record.
///
/// # Adequacy
///
/// - hypothesis: L3 — a pipe's read waits for its write, and a cancel deletes a
///   pending read.
/// - witness: `io::fd::test::echo`
/// - witness: `io::fd::test::cancel`
fn readiness(
    key: Key,
    fd: RawFd,
    ready: Ready,
    change: Change,
) -> Result<::libc::kevent, RuntimeError>
{
    let ident = usize::try_from(fd).map_err(|_negative| RuntimeError::Kernel(Errno::BADF))?;
    let filter = match ready {
        Ready::Readable => ::libc::EVFILT_READ,
        Ready::Writable => ::libc::EVFILT_WRITE,
    };
    // Each slot has its own registration of a descriptor that several
    // slots wait on: the user data is part of the registration's name.
    let flags = match change {
        Change::Add => ::libc::EV_ADD | ::libc::EV_ONESHOT,
        Change::Delete => ::libc::EV_DELETE,
    } | ::libc::EV_UDATA_SPECIFIC;
    Ok(::libc::kevent {
        ident,
        filter,
        flags,
        fflags: 0,
        data: 0,
        udata: udata(key),
    })
}

/// The change of the timer of the slot `key`, of the span `span`.
///
/// # Specification
///
/// - provides: the kernel's event that adds or deletes the timer named by
///   `key`, in nanoseconds.
/// - panics: none.
/// - executable: none — the event is the kernel's record.
///
/// # Adequacy
///
/// - hypothesis: L3 — a timer of one millisecond completes after its span, and
///   the scope's end deletes a timer of a minute.
/// - witness: `io::fd::test::timer`
/// - witness: `io::fd::test::timer_in_flight`
fn timer(
    key: Key,
    change: Change,
    span: Duration,
) -> ::libc::kevent
{
    let flags = match change {
        Change::Add => ::libc::EV_ADD | ::libc::EV_ONESHOT,
        Change::Delete => ::libc::EV_DELETE,
    };
    ::libc::kevent {
        ident: usize::from(key),
        filter: ::libc::EVFILT_TIMER,
        flags,
        fflags: ::libc::NOTE_NSECONDS,
        data: isize::try_from(span.as_nanos()).unwrap_or(isize::MAX),
        udata: udata(key),
    }
}

/// The negated error number of the thread's last refusal.
///
/// # Specification
///
/// trivial.
fn refusal() -> i32
{
    ::std::io::Error::last_os_error()
        .raw_os_error()
        .unwrap_or(::libc::EIO)
        .saturating_neg()
}

/// A completion's result of a call that returned `got`: the count or the
/// descriptor, or the negated error number of the refusal.
///
/// # Specification
///
/// trivial.
fn result_of(got: isize) -> i32
{
    if got < 0 {
        refusal()
    }
    else {
        i32::try_from(got).unwrap_or(i32::MAX)
    }
}

/// The completion's result of `outcome`: zero, or the negated error number
/// of its refusal.
///
/// # Specification
///
/// trivial.
fn outcome_of(outcome: &::std::io::Result<()>) -> i32
{
    match *outcome {
        Ok(()) => 0,
        Err(ref error) => error.raw_os_error().unwrap_or(::libc::EIO).saturating_neg(),
    }
}

/// Does the call of `wait`, whose descriptor is ready with `count` bytes to
/// read or of room to write.
///
/// # Specification
///
/// - provides: the call's result, or nothing when the call would block, so the
///   slot waits again.
/// - panics: none.
/// - executable: none — the call is the kernel's.
///
/// # Adequacy
///
/// - hypothesis: L3 — a pipe's write and read move four bytes, and an accept
///   gives a connection.
/// - witness: `io::fd::test::echo`
/// - witness: `io::socket::test::socket::accept`
/// - witness: `io::socket::test::socket::recv`
fn perform(
    wait: Wait,
    count: isize,
    end: End,
) -> Option<i32>
{
    let room = usize::try_from(count).unwrap_or(0);
    // A readiness that counts no byte while the far end is open would make a
    // call that blocks: the slot waits again.
    let take = |len: usize| -> Option<usize> {
        let take = len.min(room).min(MOST);
        if take == 0 && len != 0 && end == End::Open {
            None
        }
        else {
            Some(take)
        }
    };
    let got = match wait {
        Wait::Read { fd, into, len } => {
            let take = take(len)?;
            // SAFETY: the bytes are lent for the scope's life, and the scope's
            // end deletes the registration before the borrow ends; `take` is
            // at most their count.
            unsafe { ::libc::read(fd, into.as_ptr().cast(), take) }
        },
        Wait::Recv { fd, into, len } => {
            let take = take(len)?;
            // SAFETY: as for the read.
            unsafe { ::libc::recv(fd, into.as_ptr().cast(), take, 0) }
        },
        Wait::Write { fd, from, len } => {
            let take = take(len)?;
            // SAFETY: the bytes are lent for the scope's life, and the scope's
            // end deletes the registration before the borrow ends; `take` is
            // at most their count.
            unsafe { ::libc::write(fd, from.as_ptr().cast_const().cast(), take) }
        },
        Wait::Accept { fd, peer, len } => {
            // SAFETY: the peer's storage and its length are lent for the
            // scope's life, and the scope's end deletes the registration
            // before the borrow ends.
            let got = unsafe { ::libc::accept(fd, peer.as_ptr().cast(), len.as_ptr()) };
            isize::try_from(got).unwrap_or(-1)
        },
        Wait::Timer => return Some(0),
        Wait::Idle => return None,
    };
    let res = result_of(got);
    if res == Errno::AGAIN.raw_os_error().saturating_neg() {
        None
    }
    else {
        Some(res)
    }
}

/// Records the result `res` in the slot `key` of `table`.
///
/// # Specification
///
/// - ensures: the slot holds the completion.
/// - fails: `Unknown` when the table holds no such slot.
/// - panics: none.
/// - executable: none — the slot's state is the table's.
///
/// # Adequacy
///
/// - hypothesis: L3 — each member's test reads its completion.
/// - witness: `io::fd::test::echo`
fn complete(
    table: &Table,
    key: Key,
    res: i32,
) -> Result<(), RuntimeError>
{
    if table.complete(key, Cqe::new(res)) == Lookup::Missing {
        return Err(RuntimeError::Unknown(
            u64::try_from(usize::from(key)).unwrap_or(u64::MAX),
        ));
    }
    Ok(())
}

/// The kqueue adapter: the kernel's queue, what each slot waits for, the
/// changes that the next `wait` hands the kernel, the kernel's events, and
/// the completions of the members that did not wait.
#[non_exhaustive]
pub struct Kqueue
{
    /// The kernel's queue.
    kq: OwnedFd,
    /// For each slot, what it waits for.
    waits: Box<[Wait]>,
    /// The changes of registrations that the next `wait` hands the kernel:
    /// at most an add and a delete for each slot.
    changes: Vec<::libc::kevent>,
    /// The events that the kernel gives back, one for each slot at most.
    events: Box<[::libc::kevent]>,
    /// The completions of members that did not wait, one for each slot at
    /// most, which the next `wait` records.
    done: Vec<(Key, i32)>,
}

impl Kqueue
{
    /// Registers the readiness that `wait` needs for the slot `key`.
    ///
    /// # Specification
    ///
    /// - ensures: on success, the slot waits for `wait`, and the next `wait`
    ///   hands the kernel its registration.
    /// - fails: `Unknown` for a slot past the table or a member that waits on
    ///   no descriptor, and `Kernel(EBADF)` for a negative descriptor.
    /// - panics: none.
    /// - executable: none — the registration is the kernel's.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — a pipe's read waits for its write.
    /// - witness: `io::fd::test::echo`
    fn arm(
        &mut self,
        key: Key,
        wait: Wait,
    ) -> Result<(), RuntimeError>
    {
        let unknown = RuntimeError::Unknown(u64::try_from(usize::from(key)).unwrap_or(u64::MAX));
        let (fd, ready) = wait.readiness().ok_or(unknown)?;
        let change = readiness(key, fd, ready, Change::Add)?;
        let slot = self.waits.get_mut(usize::from(key)).ok_or(unknown)?;
        *slot = wait;
        self.changes.push(change);
        Ok(())
    }

    /// Withdraws the operation of the slot `target`: deletes its
    /// registration, and completes it with the cancelled refusal.
    ///
    /// # Specification
    ///
    /// - provides: zero when the slot waited, and the negated `ENOENT` when it
    ///   did not: its completion is the kernel's already, or follows.
    /// - fails: `Kernel(EBADF)` for a negative descriptor.
    /// - panics: none.
    /// - executable: none — the registration is the kernel's.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — a cancel of a pending read completes, and so does the
    ///   read, with the cancelled refusal; the scope's end withdraws a read, a
    ///   receive, an accept and a timer.
    /// - witness: `io::fd::test::cancel`
    /// - witness: `io::fd::test::read_in_flight`
    /// - witness: `io::fd::test::timer_in_flight`
    fn withdraw(
        &mut self,
        target: Key,
    ) -> Result<i32, RuntimeError>
    {
        let absent = Errno::NOENT.raw_os_error().saturating_neg();
        let Some(slot) = self.waits.get_mut(usize::from(target))
        else {
            return Ok(absent);
        };
        let change = match *slot {
            Wait::Idle => return Ok(absent),
            Wait::Timer => timer(target, Change::Delete, Duration::ZERO),
            wait => {
                let Some((fd, ready)) = wait.readiness()
                else {
                    return Ok(absent);
                };
                readiness(target, fd, ready, Change::Delete)?
            },
        };
        *slot = Wait::Idle;
        self.changes.push(change);
        self.done
            .push((target, Errno::CANCELED.raw_os_error().saturating_neg()));
        Ok(0)
    }
}

impl Adapter for Kqueue
{
    /// A new queue of the kernel, with room for `depth` slots.
    ///
    /// # Specification
    ///
    /// - provides: an adapter whose slots wait for nothing.
    /// - fails: the kernel's refusal of the queue.
    /// - panics: none.
    /// - executable: none — the queue is the kernel's.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — the kernel of the test host makes the queue.
    /// - witness: `runtime::test::new`
    ///
    /// # Errors
    ///
    /// The kernel's refusal of the queue.
    ///
    /// # Cost
    ///
    /// - allocation: the state of each slot, its changes, its events and its
    ///   completions, setup
    #[inline]
    fn open(depth: Depth) -> Result<Self, RuntimeError>
    {
        let kq = ::rustix::event::kqueue::kqueue().map_err(RuntimeError::Kernel)?;
        let slots = usize::from(depth);
        let blank = ::libc::kevent {
            ident: 0,
            filter: 0,
            flags: 0,
            fflags: 0,
            data: 0,
            udata: ::core::ptr::null_mut(),
        };
        Ok(Self {
            kq,
            waits: vec![Wait::Idle; slots].into_boxed_slice(),
            changes: Vec::with_capacity(slots.saturating_mul(2)),
            events: vec![blank; slots].into_boxed_slice(),
            done: Vec::with_capacity(slots),
        })
    }

    /// Registers `op`'s readiness, or does a member that does not wait.
    ///
    /// # Specification
    ///
    /// - requires: each memory that `op` lends outlives its completion.
    /// - ensures: on success, the slot of the ticket completes once.
    /// - fails: `Unsupported` for the linked pair, and `Unknown` for a slot
    ///   past the table.
    /// - panics: none.
    /// - executable: none — the registrations are the kernel's.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — each member's test completes through the queue, and
    ///   the pair is refused by name.
    /// - witness: `io::fd::test::echo`
    /// - witness: `io::fd::test::write_sync_is_refused`
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
        let key = ticket.0;
        match op {
            Op::Nop => self.done.push((key, 0)),
            Op::Read { fd, into } => {
                let wait = Wait::Read {
                    fd: fd.into(),
                    into: into.ptr(),
                    len: usize::from(into.len()),
                };
                self.arm(key, wait)?;
            },
            Op::Recv { fd, into } => {
                let wait = Wait::Recv {
                    fd: fd.into(),
                    into: into.ptr(),
                    len: usize::from(into.len()),
                };
                self.arm(key, wait)?;
            },
            Op::Write { fd, from } => {
                let wait = Wait::Write {
                    fd: fd.into(),
                    from: from.ptr(),
                    len: usize::from(from.len()),
                };
                self.arm(key, wait)?;
            },
            Op::Accept { fd, peer, len, .. } => {
                let wait = Wait::Accept {
                    fd: fd.into(),
                    peer,
                    len,
                };
                self.arm(key, wait)?;
            },
            Op::Timer { after } => {
                let unknown =
                    RuntimeError::Unknown(u64::try_from(usize::from(key)).unwrap_or(u64::MAX));
                let slot = self.waits.get_mut(usize::from(key)).ok_or(unknown)?;
                *slot = Wait::Timer;
                self.changes
                    .push(timer(key, Change::Add, Duration::from(*after)));
            },
            Op::Cancel { target } => {
                let res = self.withdraw(target.0)?;
                self.done.push((key, res));
            },
            Op::Socket {
                domain,
                ty,
                protocol,
            } => {
                let res = match ::socket2::Socket::new(domain, ty, protocol) {
                    Ok(socket) => socket.into_raw_fd(),
                    Err(error) => error.raw_os_error().unwrap_or(::libc::EIO).saturating_neg(),
                };
                self.done.push((key, res));
            },
            Op::Bind { fd, addr } => {
                // SAFETY: the operation borrows the descriptor until its
                // completion.
                let socket = unsafe { socket_of(fd) };
                self.done.push((key, outcome_of(&socket.bind(addr))));
            },
            Op::Listen { fd, backlog } => {
                // SAFETY: the operation borrows the descriptor until its
                // completion.
                let socket = unsafe { socket_of(fd) };
                self.done
                    .push((key, outcome_of(&socket.listen(c_int::from(backlog)))));
            },
            Op::WriteSync { .. } => return Err(RuntimeError::Unsupported(op.member())),
        }
        Ok(())
    }

    /// Withdraws the operation of the ticket's slot.
    ///
    /// # Specification
    ///
    /// - ensures: on success, the slot completes once, with the cancelled
    ///   refusal when it waited.
    /// - fails: `Kernel(EBADF)` for a negative descriptor.
    /// - panics: none.
    /// - executable: none — the registration is the kernel's.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — the scope's end drains a read, a receive, an accept
    ///   and a timer that wait.
    /// - witness: `io::fd::test::read_in_flight`
    /// - witness: `io::fd::test::timer_in_flight`
    /// - witness: `io::socket::test::socket::accept_in_flight`
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
        self.withdraw(ticket.0).map(|_res| ())
    }

    /// Hands the kernel the changes, waits for at least one event unless a
    /// completion waits already, and records each completion in its slot of
    /// `table`.
    ///
    /// # Specification
    ///
    /// - ensures: each completion of a member that did not wait, and of each
    ///   slot whose call the kernel's events allowed, is in its slot.
    /// - fails: the kernel's refusal of the wait, other than an interrupt, and
    ///   `Unknown` when an event names no slot.
    /// - panics: none.
    /// - executable: none — the kernel's queue is not a value that the call can
    ///   read.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — each member's test completes through the queue.
    /// - witness: `io::fd::test::echo`
    /// - witness: `io::fd::test::timer`
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
        let zero = ::libc::timespec {
            tv_sec: 0,
            tv_nsec: 0,
        };
        let timeout = if self.done.is_empty() {
            ::core::ptr::null()
        }
        else {
            &raw const zero
        };
        let changes =
            c_int::try_from(self.changes.len()).map_err(|_overflow| RuntimeError::Full)?;
        let room = c_int::try_from(self.events.len()).map_err(|_overflow| RuntimeError::Full)?;
        // SAFETY: the change list and the event list are this adapter's
        // memory for the call, of the counts given. Each registration names a
        // descriptor that its operation borrows until the operation completes
        // or the scope's end deletes the registration.
        let got = unsafe {
            ::libc::kevent(
                self.kq.as_raw_fd(),
                self.changes.as_ptr(),
                changes,
                self.events.as_mut_ptr(),
                room,
                timeout,
            )
        };
        self.changes.clear();
        let got = match usize::try_from(got) {
            Ok(got) => got,
            Err(_negative) => {
                let errno = Errno::from_raw_os_error(refusal().saturating_neg());
                if errno != Errno::INTR {
                    return Err(RuntimeError::Kernel(errno));
                }
                0
            },
        };
        for (key, res) in self.done.drain(..) {
            complete(table, key, res)?;
        }
        let Self {
            ref events,
            ref mut waits,
            ref mut changes,
            ..
        } = *self;
        for event in events.iter().take(got) {
            let data = u64::try_from(event.udata.addr()).unwrap_or(u64::MAX);
            let key = Key::try_from(data).map_err(|_overflow| RuntimeError::Unknown(data))?;
            let slot = waits
                .get_mut(usize::from(key))
                .ok_or(RuntimeError::Unknown(data))?;
            let wait = *slot;
            if matches!(wait, Wait::Idle) {
                // The event of a delete that found its registration gone.
                continue;
            }
            if event.flags & ::libc::EV_ERROR != 0 {
                // The kernel refused the registration: its operation fails.
                *slot = Wait::Idle;
                let errno = i32::try_from(event.data).unwrap_or(::libc::EIO);
                complete(table, key, errno.saturating_neg())?;
                continue;
            }
            let end = if event.flags & ::libc::EV_EOF != 0 {
                End::Closed
            }
            else {
                End::Open
            };
            if let Some(res) = perform(wait, event.data, end) {
                *slot = Wait::Idle;
                complete(table, key, res)?;
            }
            else if let Some((fd, ready)) = wait.readiness() {
                changes.push(readiness(key, fd, ready, Change::Add)?);
            }
        }
        Ok(())
    }
}
