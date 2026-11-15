//! The runtime: the ring, the run loop that drives one scope's future, and
//! the scope's end.

use ::core::cell::RefCell;
use ::core::pin::pin;
use ::core::task::Poll;
use ::gandr_runtime_uring::IoUring;
use ::gandr_runtime_uring::arg::Count;
use ::gandr_runtime_uring::arg::Flags;
use ::gandr_runtime_uring::arg::UserData;
use ::rustix::io::Errno;

use crate::completion::Cqe;
use crate::error::RuntimeError;
use crate::scope::Scope;
use crate::submission::Depth;
use crate::submission::Hold;
use crate::submission::Key;
use crate::submission::Lookup;
use crate::submission::Table;

/// The runtime: the kernel's ring, which one run of a scope drives.
#[repr(transparent)]
#[non_exhaustive]
pub struct Runtime
{
    /// The kernel's ring.
    io: IoUring<'static>,
}

impl Runtime
{
    /// The count of the ring's entries, and of the table's slots.
    const IO_URING_ENTRIES: u16 = 4096;

    /// A runtime on a new ring of the kernel.
    ///
    /// # Specification
    ///
    /// - provides: a runtime whose ring has `IO_URING_ENTRIES` entries.
    /// - fails: the kernel's error when it refuses the ring.
    /// - panics: none.
    /// - executable: none — the ring is the kernel's, and the call holds
    ///   nothing to check it against.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — the kernel of the test host makes the ring.
    /// - witness: `runtime::test::new`
    ///
    /// # Errors
    ///
    /// - [`RuntimeError::Kernel`] when the kernel refuses the ring.
    /// - [`RuntimeError::Ring`] when the ring's crate refuses it with no error
    ///   number.
    #[inline]
    pub fn new() -> Result<Self, RuntimeError>
    {
        let io = IoUring::builder()
            .entries(Count(u32::from(Self::IO_URING_ENTRIES)))
            .build()?;
        Ok(Self { io })
    }

    /// A context whose waker does nothing: the run loop polls the scope's
    /// future after each reap, so no task wakes it.
    ///
    /// # Specification
    ///
    /// trivial.
    const fn noop_cx() -> ::core::task::Context<'static>
    {
        let waker = ::core::task::Waker::noop();
        ::core::task::Context::from_waker(waker)
    }

    /// Runs the scope's future that `start` makes, and ends the scope with
    /// it.
    ///
    /// # Specification
    ///
    /// - ensures: after the run, the kernel holds no operation of the scope,
    ///   and no completion of the scope waits in the ring.
    /// - provides: the future's output.
    /// - fails: the kernel's error when a submission, a wait or a cancel fails,
    ///   and `Unknown` when a completion names no slot.
    /// - panics: none.
    /// - executable: none — the kernel's state of the ring is not a value that
    ///   the call can read.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — a scope whose future returns while an accept or a
    ///   receive stays in the kernel ends with the table drained.
    /// - witness: `io::socket::test::socket::accept_in_flight`
    /// - witness: `io::socket::test::socket::recv_in_flight`
    /// - witness: `runtime::test::run::closure`
    ///
    /// # Errors
    ///
    /// - [`RuntimeError::Kernel`] when a submission, a wait or a cancel fails.
    /// - [`RuntimeError::Unknown`] when a completion names no slot.
    /// - [`RuntimeError::Full`] when the queue has no room for a cancel.
    ///
    /// # Cost
    ///
    /// - allocation: the table's slots, setup
    #[inline]
    pub fn run<'env, T, F>(
        self,
        start: F,
    ) -> Result<T, RuntimeError>
    where
        F: for<'tsk> AsyncFnOnce(&'tsk Scope<'tsk, 'env>) -> T,
    {
        let io = RefCell::new(self.io);
        let table = Table::new(Depth::from(Self::IO_URING_ENTRIES));

        let scope = Scope::new(&io, &table);
        let mut future = pin!(start(&scope));

        loop {
            if let Poll::Ready(val) = future.as_mut().poll(&mut Self::noop_cx()) {
                // The main future is ready, and the scope ends with it. Each
                // operation that the kernel still holds is cancelled, and
                // the run waits for every completion before it returns, so
                // the kernel holds no operation of the scope after the run.
                end(&io, &table)?;
                return Ok(val);
            }

            // Submit the entries that the scope prepared, wait for at least
            // one completion, and record each in its slot.
            reap(&io, &table)?;
        }
    }
}

/// The bit of the user data that marks a cancel's own completion. The other
/// bits name the slot of the operation that the cancel ends, so a refused
/// cancel names its operation. A key of the table is below the ring's depth,
/// so no request's user data holds the bit.
const CANCEL: u64 = 1 << 63;

/// Ends a scope: submits a cancel for each operation that the kernel holds,
/// then drains every completion, two for each cancel.
///
/// # Specification
///
/// - ensures: the table is drained.
/// - fails: the kernel's error when a submission or a wait fails, `Cancel` with
///   the operation's slot when a cancel fails, and `Unknown` when a completion
///   names no slot.
/// - panics: none.
/// - executable: none — the kernel's state of the ring is not a value that the
///   call can read.
///
/// # Adequacy
///
/// - hypothesis: L3 — the end drains a scope that leaves an accept, and one
///   that leaves a receive, in the kernel.
/// - witness: `io::socket::test::socket::accept_in_flight`
/// - witness: `io::socket::test::socket::recv_in_flight`
fn end(
    io: &RefCell<IoUring<'static>>,
    table: &Table,
) -> Result<(), RuntimeError>
{
    if table.hold() == Hold::Drained {
        return Ok(());
    }
    {
        let mut ring = io.borrow_mut();
        let mut squ = ring.squeue();
        // The kernel takes every prepared entry, so the queue has room for a
        // cancel of each slot that the table holds.
        squ.submit()?;
        for key in table.in_kernel() {
            let data = u64::try_from(key).map_err(|_overflow| RuntimeError::Full)?;
            let mut sqe = squ.get_sqe().ok_or(RuntimeError::Full)?;
            // SAFETY: a cancel by user data reads no pointer and names no
            // descriptor.
            unsafe {
                sqe.prep_cancel64(UserData(data), Flags(0_i32));
            }
            // SAFETY: the user data is a number that the kernel only hands
            // back.
            unsafe {
                sqe.set_data64(UserData(CANCEL | data));
            }
        }
    }
    while table.hold() == Hold::Held {
        reap(io, table)?;
    }
    Ok(())
}

/// Submits the prepared entries, waits for at least one completion, and
/// records each ready completion in its slot of `table`.
///
/// # Specification
///
/// - ensures: each completion that was ready is in its slot.
/// - fails: the kernel's error when the submission or the wait fails; `Cancel`
///   with the operation's slot when a cancel fails other than with `ENOENT` or
///   `EALREADY`; `Unknown` when a completion names no slot.
/// - panics: none.
/// - executable: none — the kernel's state of the ring is not a value that the
///   call can read.
///
/// # Adequacy
///
/// - hypothesis: L3 — a thousand no-ops each complete into their slots, and the
///   cancels of a scope's end complete with no refusal.
/// - witness: `tests::path::request::a_request_allocates_nothing_after_the_start`
/// - witness: `io::socket::test::socket::accept_in_flight`
pub fn reap(
    io: &RefCell<IoUring<'static>>,
    table: &Table,
) -> Result<(), RuntimeError>
{
    let mut io = io.borrow_mut();
    let (mut squ, mut cqu) = io.queues();
    squ.submit_and_wait(Count(1))?;

    for cqe in cqu.ready() {
        let UserData(data) = cqe.user_data();
        if data & CANCEL != 0 {
            // A cancel finds its operation, or finds it already complete or
            // past the point of a cancel; the operation's own completion
            // follows in each case. Any other refusal names the operation's
            // slot.
            match Cqe::from(cqe).done() {
                Ok(()) | Err(RuntimeError::Kernel(Errno::NOENT | Errno::ALREADY)) => {},
                Err(RuntimeError::Kernel(errno)) => {
                    return Err(RuntimeError::Cancel {
                        data: data & !CANCEL,
                        errno,
                    });
                },
                Err(error) => return Err(error),
            }
            continue;
        }
        let key = Key::try_from(data).map_err(|_overflow| RuntimeError::Unknown(data))?;
        if table.complete(key, Cqe::from(cqe)) == Lookup::Missing {
            return Err(RuntimeError::Unknown(data));
        }
    }
    Ok(())
}

/// The runtime's tests and their harness.
#[cfg(test)]
pub mod test
{
    use super::*;

    /// The harness of the runtime's tests.
    pub mod harness
    {
        use super::*;

        /// A runtime on a new ring of the kernel.
        ///
        /// # Specification
        ///
        /// trivial.
        pub fn new() -> Runtime
        {
            Runtime::new().unwrap()
        }
    }

    #[test]
    #[cfg_attr(
        miri,
        ignore = "it sets up a ring of the kernel, which Miri cannot run"
    )]
    fn new()
    {
        self::harness::new();
    }

    mod run
    {
        use super::*;

        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring of the kernel, which Miri cannot run"
        )]
        fn closure()
        {
            let data = &mut vec![];
            crate::test::harness::runtime::new()
                .run(async |_scope| {
                    data.push(0u8);
                    Ok::<_, RuntimeError>(())
                })
                .unwrap()
                .unwrap();
            assert_eq!(data.as_slice(), &[0u8]);
        }

        /// A request past the table's depth waits for a drain. When the
        /// drain frees no slot, because every completion still waits for its
        /// reader, the request gives the stated result of a full table. Once
        /// the completions drop, their slots come free again.
        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring of the kernel, which Miri cannot run"
        )]
        fn full()
        {
            let nop = |sqe: &mut ::gandr_runtime_uring::Sqe64<'_>| {
                // SAFETY: a no-op reads no pointer and names no descriptor.
                unsafe {
                    sqe.prep_nop();
                }
            };
            let depth = usize::from(Runtime::IO_URING_ENTRIES);
            crate::test::harness::runtime::new()
                .run(async |scope| {
                    let held = ::core::iter::repeat_with(|| scope.request(nop))
                        .take(depth)
                        .collect::<Vec<_>>();
                    let error = scope.request(nop).await.err();
                    assert_eq!(error, Some(RuntimeError::Full));
                    drop(held);
                    scope.request(nop).await.unwrap();
                })
                .unwrap();
        }
    }
}
