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

/// The runtime: the kernel's ring and the table of its operations, which
/// each run of a scope drives in turn.
#[non_exhaustive]
pub struct Runtime
{
    /// The kernel's ring.
    io: RefCell<IoUring<'static>>,
    /// The table of the operations in flight: one slot for each entry of the
    /// ring.
    table: Table,
    /// Whether a run failed, so that the kernel can hold its operations.
    spent: Spent,
}

/// Whether a run of the runtime failed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Spent
{
    /// Each run so far ended with the table drained.
    No,
    /// A run failed, and the kernel can hold its operations.
    Yes,
}

impl Runtime
{
    /// A runtime on a new ring of the kernel of `depth` entries, with a
    /// table of `depth` slots.
    ///
    /// # Specification
    ///
    /// - provides: a runtime whose ring has `depth` entries.
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
    ///
    /// # Cost
    ///
    /// - allocation: the table's slots, setup
    #[inline]
    pub fn with_depth(depth: Depth) -> Result<Self, RuntimeError>
    {
        let io = IoUring::builder()
            .entries(Count(u32::from(u16::from(depth))))
            .build()?;
        Ok(Self {
            io: RefCell::new(io),
            table: Table::new(depth),
            spent: Spent::No,
        })
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
    /// it. A later run uses the same ring and table.
    ///
    /// # Specification
    ///
    /// - requires: no earlier run failed.
    /// - ensures: after a run that gives `Ok`, the kernel holds no operation of
    ///   the scope, no completion of the scope waits in the ring, and the
    ///   runtime takes a later run. After a run that gives `Err`, the runtime
    ///   is spent.
    /// - provides: the future's output.
    /// - fails: `Spent` when an earlier run failed; the kernel's error when a
    ///   submission, a wait or a cancel fails; and `Unknown` when a completion
    ///   names no slot.
    /// - panics: none.
    /// - executable: none — the kernel's state of the ring is not a value that
    ///   the call can read.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — a scope whose future returns while an accept or a
    ///   receive stays in the kernel ends with the table drained, and a second
    ///   run on the same runtime finds each slot free.
    /// - witness: `io::socket::test::socket::accept_in_flight`
    /// - witness: `io::socket::test::socket::recv_in_flight`
    /// - witness: `runtime::test::run::closure`
    /// - witness: `runtime::test::run::again`
    /// - witness: `tests::path::request::a_later_run_allocates_nothing`
    ///
    /// # Errors
    ///
    /// - [`RuntimeError::Spent`] when an earlier run failed.
    /// - [`RuntimeError::Kernel`] when a submission, a wait or a cancel fails.
    /// - [`RuntimeError::Unknown`] when a completion names no slot.
    /// - [`RuntimeError::Full`] when the queue has no room for a cancel.
    #[inline]
    pub fn run<'env, T, F>(
        &mut self,
        start: F,
    ) -> Result<T, RuntimeError>
    where
        F: for<'tsk> AsyncFnOnce(&'tsk Scope<'tsk, 'env>) -> T,
    {
        if self.spent == Spent::Yes {
            return Err(RuntimeError::Spent);
        }
        let ran = Self::drive(&self.io, &self.table, start);
        if ran.is_err() {
            self.spent = Spent::Yes;
        }
        ran
    }

    /// Drives the scope's future on `io` and `table` to its end.
    ///
    /// # Specification
    ///
    /// - ensures: on `Ok`, the kernel holds no operation of the scope.
    /// - provides: the future's output.
    /// - fails: the kernel's error, `Unknown` or `Full`, as `run` states.
    /// - panics: none.
    /// - executable: none — the kernel's state of the ring is not a value that
    ///   the call can read.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — the run's witnesses drive each scope through it.
    /// - witness: `runtime::test::run::closure`
    /// - witness: `io::socket::test::socket::accept_in_flight`
    fn drive<'env, T, F>(
        io: &RefCell<IoUring<'static>>,
        table: &Table,
        start: F,
    ) -> Result<T, RuntimeError>
    where
        F: for<'tsk> AsyncFnOnce(&'tsk Scope<'tsk, 'env>) -> T,
    {
        let scope = Scope::new(io, table);
        let mut future = pin!(start(&scope));

        loop {
            if let Poll::Ready(val) = future.as_mut().poll(&mut Self::noop_cx()) {
                // The main future is ready, and the scope ends with it. Each
                // operation that the kernel still holds is cancelled, and
                // the run waits for every completion before it returns, so
                // the kernel holds no operation of the scope after the run.
                end(io, table)?;
                return Ok(val);
            }

            // Submit the entries that the scope prepared, wait for at least
            // one completion, and record each in its slot.
            reap(io, table)?;
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

        /// The depth of the tests' rings.
        pub const DEPTH: u16 = 4096;

        /// A runtime on a new ring of the kernel of `DEPTH` entries.
        ///
        /// # Specification
        ///
        /// trivial.
        pub fn new() -> Runtime
        {
            Runtime::with_depth(Depth::from(DEPTH)).unwrap()
        }

        /// A request of a no-op.
        ///
        /// # Specification
        ///
        /// trivial.
        pub fn nop(sqe: &mut ::gandr_runtime_uring::Sqe64<'_>)
        {
            // SAFETY: a no-op reads no pointer and names no descriptor.
            unsafe {
                sqe.prep_nop();
            }
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
            use crate::test::harness::runtime::nop;
            let depth = usize::from(crate::test::harness::runtime::DEPTH);
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

        /// Each run of one runtime finds every slot of its table free: the
        /// table takes `depth` requests and refuses the next, and each of
        /// the `depth` completes. The second run reads the same.
        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring of the kernel, which Miri cannot run"
        )]
        fn again()
        {
            use crate::test::harness::runtime::nop;
            let depth = 4_u16;
            let mut runtime = Runtime::with_depth(Depth::from(depth)).unwrap();
            for _round in 0 .. 2_u8 {
                runtime
                    .run(async |scope| {
                        let held = ::core::iter::repeat_with(|| scope.request(nop))
                            .take(usize::from(depth))
                            .collect::<Vec<_>>();
                        let error = scope.request(nop).await.err();
                        assert_eq!(error, Some(RuntimeError::Full));
                        for completion in held {
                            completion.await.unwrap();
                        }
                    })
                    .unwrap();
            }
        }
    }
}
