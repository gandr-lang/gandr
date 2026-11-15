//! The completion of one request: the future that reads its slot of the
//! table, and the kernel's result that it gives.

use ::core::marker::PhantomData;
use ::core::pin::Pin;
use ::core::task::Context;
use ::core::task::Poll;
use ::gandr_runtime_uring::Cqe16;
use ::rustix::io::Errno;
use ::std::os::fd::FromRawFd as _;
use ::std::os::fd::OwnedFd;

use crate::error::RuntimeError;
use crate::submission::Key;
use crate::submission::Table;

/// The kernel's completion of one operation, its result copied out of the
/// ring: a count or a descriptor when it is not negative, and the negated
/// error number when it is.
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct Cqe
{
    /// The kernel's result.
    res: i32,
}

impl From<Cqe16<'_>> for Cqe
{
    /// The result of the ring's entry `cqe`.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn from(cqe: Cqe16<'_>) -> Self
    {
        Self { res: cqe.res().0 }
    }
}

/// A count of bytes that an operation moved.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Count(usize);

impl From<Count> for usize
{
    /// The count.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn from(count: Count) -> Self
    {
        count.0
    }
}

impl Cqe
{
    /// A completion whose result is zero: a count of no bytes.
    #[cfg(test)]
    pub(crate) const ZERO: Self = Self { res: 0 };

    /// The kernel's refusal that a negative result names.
    ///
    /// # Specification
    ///
    /// trivial.
    fn refusal(self) -> RuntimeError
    {
        RuntimeError::Kernel(Errno::from_raw_os_error(self.res.saturating_neg()))
    }

    /// The outcome of an operation that gives no value.
    ///
    /// # Specification
    ///
    /// - fails: the kernel's error when the result is negative.
    /// - panics: none.
    /// - executable: none — the result is the kernel's, and the call holds
    ///   nothing to check it against.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — a bind and a listen on a fresh socket give no
    ///   refusal.
    /// - witness: `io::socket::test::socket::listen`
    /// - witness: `completion::test::cqe::a_count_is_the_result`
    /// - witness: `completion::test::cqe::a_negative_result_is_the_kernel_s_error`
    pub fn done(self) -> Result<(), RuntimeError>
    {
        if self.res.is_negative() {
            Err(self.refusal())
        }
        else {
            Ok(())
        }
    }

    /// The count of bytes that the operation moved.
    ///
    /// # Specification
    ///
    /// - provides: the result as a count.
    /// - fails: the kernel's error when the result is negative.
    /// - panics: none.
    /// - executable: none — the result is the kernel's, and the call holds
    ///   nothing to check it against.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — a receive of four bytes gives a count of four.
    /// - witness: `io::socket::test::socket::recv`
    /// - witness: `completion::test::cqe::a_count_is_the_result`
    /// - witness: `completion::test::cqe::a_negative_result_is_the_kernel_s_error`
    pub fn count(self) -> Result<Count, RuntimeError>
    {
        usize::try_from(self.res)
            .map(Count)
            .map_err(|_negative| self.refusal())
    }

    /// The descriptor that the operation made.
    ///
    /// # Safety
    ///
    /// - unsafe invariants: the operation makes a descriptor when it does not
    ///   fail, as a socket's creation and an accept do, and nothing else owns
    ///   it.
    ///
    /// # Specification
    ///
    /// - provides: the descriptor, owned.
    /// - fails: the kernel's error when the result is negative.
    /// - panics: none.
    /// - executable: none — the result is the kernel's, and the call holds
    ///   nothing to check it against.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — a socket's creation and an accept each give a
    ///   descriptor that the test binds, listens on or drops.
    /// - witness: `io::socket::test::socket::new`
    /// - witness: `io::socket::test::socket::accept`
    pub unsafe fn descriptor(self) -> Result<OwnedFd, RuntimeError>
    {
        if self.res.is_negative() {
            return Err(self.refusal());
        }
        // SAFETY: the caller's invariant: the result is a descriptor that
        // nothing else owns.
        Ok(unsafe { OwnedFd::from_raw_fd(self.res) })
    }
}

/// Where a completion stands.
enum State
{
    /// The request found no slot, for this reason.
    Refused(RuntimeError),
    /// The operation holds slot `key`.
    Waiting(Key),
    /// The completion gave its result.
    Read,
}

/// The completion of one request: it reads the request's slot of the table
/// when the run loop records the kernel's completion there. It carries the
/// scope's brand, so it cannot leave the scope.
pub struct Completion<'tsk>
{
    /// The table that holds the request's slot.
    table: &'tsk Table,
    /// Where the completion stands.
    state: State,
    /// The scope's brand.
    phd_tsk: PhantomData<&'tsk mut &'tsk ()>,
}

impl<'tsk> Completion<'tsk>
{
    /// The completion of the request in slot `key` of `table`.
    ///
    /// # Specification
    ///
    /// trivial.
    pub(crate) const fn new(
        table: &'tsk Table,
        key: Key,
    ) -> Self
    {
        Completion {
            table,
            state: State::Waiting(key),
            phd_tsk: PhantomData,
        }
    }

    /// The completion of a request that found no slot, for `error`.
    ///
    /// # Specification
    ///
    /// trivial.
    pub(crate) const fn refused(
        table: &'tsk Table,
        error: RuntimeError,
    ) -> Self
    {
        Completion {
            table,
            state: State::Refused(error),
            phd_tsk: PhantomData,
        }
    }
}

impl Drop for Completion<'_>
{
    /// Leaves the request's slot to the kernel's completion, when the
    /// completion did not read it.
    ///
    /// # Specification
    ///
    /// trivial.
    fn drop(&mut self)
    {
        if let State::Waiting(key) = self.state {
            self.table.abandon(key);
        }
    }
}

impl Future for Completion<'_>
{
    type Output = Result<Cqe, RuntimeError>;

    /// The kernel's completion of the request, once the run loop records it
    /// in the slot.
    ///
    /// # Specification
    ///
    /// - ensures: on `Ready(Ok)`, the slot is free.
    /// - provides: the kernel's completion.
    /// - fails: the reason of a request that found no slot, `Full` or the error
    ///   of a drain, and `Read` when the completion already gave its result.
    /// - panics: none.
    /// - executable: none — the slot's state is a cell that no predicate of the
    ///   call reads before it.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — a request past the table's depth reads `Full`, and a
    ///   thousand requests each read their completion.
    /// - witness: `runtime::test::run::full`
    /// - witness: `tests::path::request::a_request_allocates_nothing_after_the_start`
    /// - witness: `completion::test::completion::waits_then_reads_then_refuses_a_second_read`
    /// - witness: `completion::test::completion::a_refused_request_gives_its_reason`
    fn poll(
        self: Pin<&mut Self>,
        _cx: &mut Context<'_>,
    ) -> Poll<Self::Output>
    {
        let this = self.get_mut();
        match this.state {
            State::Refused(error) => Poll::Ready(Err(error)),
            State::Read => Poll::Ready(Err(RuntimeError::Read)),
            State::Waiting(key) => {
                let Some(cqe) = this.table.read(key)
                else {
                    return Poll::Pending;
                };
                this.state = State::Read;
                Poll::Ready(Ok(cqe))
            },
        }
    }
}

/// The completion's tests. No ring takes part, so Miri runs each one.
#[cfg(test)]
mod test
{
    use ::core::pin::Pin;
    use ::core::task::Context;
    use ::core::task::Poll;
    use ::core::task::Waker;

    use super::*;
    use crate::io::buf::Buf;
    use crate::submission::Depth;
    use crate::submission::Hold;

    /// The outcomes of a completion's result.
    mod cqe
    {
        use super::*;

        #[test]
        fn a_count_is_the_result()
        {
            assert_eq!(Cqe { res: 4 }.count().map(usize::from), Ok(4));
            assert_eq!(Cqe { res: 4 }.done(), Ok(()));
        }

        #[test]
        fn a_negative_result_is_the_kernel_s_error()
        {
            let cqe = Cqe { res: -22 };
            assert_eq!(cqe.done(), Err(RuntimeError::Kernel(Errno::INVAL)));
            assert_eq!(
                cqe.count().map(usize::from),
                Err(RuntimeError::Kernel(Errno::INVAL))
            );
            // SAFETY: a negative result makes no descriptor, so the call
            // takes no descriptor's ownership.
            let descriptor = unsafe { cqe.descriptor() };
            assert_eq!(descriptor.err(), Some(RuntimeError::Kernel(Errno::INVAL)));
        }

        #[test]
        fn a_count_prefixes_the_lent_buffer()
        {
            let mut bytes = [1_u8, 2, 3, 4];
            let got = Buf::from(&mut bytes[..]).prefix(Count(2));
            assert_eq!(got.as_deref(), Some([1_u8, 2].as_slice()));
            let past = Buf::from(&mut bytes[..]).prefix(Count(5));
            assert_eq!(past, None);
        }
    }

    /// The states of a completion over its slot.
    mod completion
    {
        use super::*;

        #[test]
        fn waits_then_reads_then_refuses_a_second_read()
        {
            let table = Table::new(Depth::from(1_u16));
            let key = table.take().unwrap();
            let mut completion = Completion::new(&table, key);
            let mut cx = Context::from_waker(Waker::noop());
            assert!(Pin::new(&mut completion).poll(&mut cx).is_pending());
            table.complete(key, Cqe { res: 3 });
            let Poll::Ready(Ok(cqe)) = Pin::new(&mut completion).poll(&mut cx)
            else {
                panic!("the completion reads its slot once the kernel completes it");
            };
            assert_eq!(cqe.count().map(usize::from), Ok(3));
            assert!(matches!(
                Pin::new(&mut completion).poll(&mut cx),
                Poll::Ready(Err(RuntimeError::Read))
            ));
            assert_eq!(table.take(), Some(key));
        }

        #[test]
        fn a_dropped_completion_leaves_its_slot_to_the_kernel()
        {
            let table = Table::new(Depth::from(1_u16));
            let key = table.take().unwrap();
            drop(Completion::new(&table, key));
            assert_eq!(table.take(), None);
            assert_eq!(table.hold(), Hold::Held);
            table.complete(key, Cqe::ZERO);
            assert_eq!(table.hold(), Hold::Drained);
            assert_eq!(table.take(), Some(key));
        }

        #[test]
        fn a_refused_request_gives_its_reason()
        {
            let table = Table::new(Depth::from(1_u16));
            let mut completion = Completion::refused(&table, RuntimeError::Full);
            let mut cx = Context::from_waker(Waker::noop());
            assert!(matches!(
                Pin::new(&mut completion).poll(&mut cx),
                Poll::Ready(Err(RuntimeError::Full))
            ));
        }
    }
}
