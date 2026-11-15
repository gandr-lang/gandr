//! The runtime: the adapter of the kernel, the run loop that drives one
//! scope's future, and the scope's end.

use ::core::cell::RefCell;
use ::core::pin::pin;
use ::core::task::Poll;

use crate::adapter::Adapter;
use crate::adapter::Native;
use crate::error::RuntimeError;
use crate::op::Ticket;
use crate::scope::Scope;
use crate::submission::Depth;
use crate::submission::Hold;
use crate::submission::Table;

/// The runtime: the adapter of the kernel, which one run of a scope drives.
/// A program takes the target's adapter, [`Native`]; a test names one.
#[repr(transparent)]
#[non_exhaustive]
pub struct Runtime<A = Native>
where
    A: Adapter,
{
    /// The kernel's adapter.
    adapter: A,
}

impl Runtime
{
    /// A runtime on a new queue of the target's kernel.
    ///
    /// # Specification
    ///
    /// - provides: a runtime whose queue has `DEPTH` entries.
    /// - fails: the kernel's error when it refuses the queue.
    /// - panics: none.
    /// - executable: none — the queue is the kernel's, and the call holds
    ///   nothing to check it against.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — the kernel of the test host makes the queue.
    /// - witness: `runtime::test::new`
    ///
    /// # Errors
    ///
    /// - [`RuntimeError::Kernel`] when the kernel refuses the queue.
    /// - [`RuntimeError::Ring`] when the ring's crate refuses it with no error
    ///   number.
    ///
    /// # Cost
    ///
    /// - allocation: the adapter's state of each slot, setup
    #[inline]
    pub fn new() -> Result<Self, RuntimeError>
    {
        Self::open()
    }
}

impl<A> Runtime<A>
where
    A: Adapter,
{
    /// The count of the queue's entries, and of the table's slots.
    const DEPTH: u16 = 4096;

    /// A runtime on a new queue of the kernel that the adapter `A` names.
    ///
    /// # Specification
    ///
    /// - provides: a runtime whose queue has `DEPTH` entries.
    /// - fails: the kernel's error when it refuses the queue.
    /// - panics: none.
    /// - executable: none — the queue is the kernel's, and the call holds
    ///   nothing to check it against.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — the kernel of the test host makes the queue.
    /// - witness: `runtime::test::new`
    ///
    /// # Errors
    ///
    /// The adapter's refusal of the queue.
    ///
    /// # Cost
    ///
    /// - allocation: the adapter's state of each slot, setup
    #[inline]
    pub fn open() -> Result<Self, RuntimeError>
    {
        let adapter = A::open(Depth::from(Self::DEPTH))?;
        Ok(Self { adapter })
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
    ///   and no completion of the scope waits in its queue.
    /// - provides: the future's output.
    /// - fails: the kernel's error when a submission, a wait or a cancel fails,
    ///   and `Unknown` when a completion names no slot.
    /// - panics: none.
    /// - executable: none — the kernel's state of the queue is not a value that
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
        F: for<'tsk> AsyncFnOnce(&'tsk Scope<'tsk, 'env, A>) -> T,
    {
        let adapter = RefCell::new(self.adapter);
        let table = Table::new(Depth::from(Self::DEPTH));

        let scope = Scope::new(&adapter, &table);
        let mut future = pin!(start(&scope));

        loop {
            if let Poll::Ready(val) = future.as_mut().poll(&mut Self::noop_cx()) {
                // The main future is ready, and the scope ends with it. Each
                // operation that the kernel still holds is cancelled, and
                // the run waits for every completion before it returns, so
                // the kernel holds no operation of the scope after the run.
                end(&adapter, &table)?;
                return Ok(val);
            }

            // Start the operations that the scope requested, wait for at
            // least one completion, and record each in its slot.
            reap(&adapter, &table)?;
        }
    }
}

/// Ends a scope: cancels each operation that the kernel holds, then drains
/// every completion, the cancels' own among them.
///
/// # Specification
///
/// - ensures: the table is drained.
/// - fails: the kernel's error when a submission or a wait fails, `Cancel` with
///   the operation's slot when a cancel fails, and `Unknown` when a completion
///   names no slot.
/// - panics: none.
/// - executable: none — the kernel's state of the queue is not a value that the
///   call can read.
///
/// # Adequacy
///
/// - hypothesis: L3 — the end drains a scope that leaves an accept, and one
///   that leaves a receive, in the kernel.
/// - witness: `io::socket::test::socket::accept_in_flight`
/// - witness: `io::socket::test::socket::recv_in_flight`
fn end<A>(
    adapter: &RefCell<A>,
    table: &Table,
) -> Result<(), RuntimeError>
where
    A: Adapter,
{
    if table.hold() == Hold::Drained {
        return Ok(());
    }
    {
        let mut adapter = adapter.borrow_mut();
        for key in table.in_kernel() {
            adapter.cancel(Ticket(key))?;
        }
    }
    while table.hold() == Hold::Held {
        reap(adapter, table)?;
    }
    Ok(())
}

/// Starts the operations that the scope requested, waits for at least one
/// completion, and records each ready completion in its slot of `table`.
///
/// # Specification
///
/// - ensures: each completion that was ready is in its slot.
/// - fails: the adapter's refusal of the wait.
/// - panics: none.
/// - executable: none — the kernel's state of the queue is not a value that the
///   call can read.
///
/// # Adequacy
///
/// - hypothesis: L3 — a thousand no-ops each complete into their slots, and the
///   cancels of a scope's end complete with no refusal.
/// - witness: `tests::path::request::a_request_allocates_nothing_after_the_start`
/// - witness: `io::socket::test::socket::accept_in_flight`
pub fn reap<A>(
    adapter: &RefCell<A>,
    table: &Table,
) -> Result<(), RuntimeError>
where
    A: Adapter,
{
    adapter.borrow_mut().wait(table)
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
            let nop = crate::op::Op::Nop;
            let depth = usize::from(Runtime::<Native>::DEPTH);
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
