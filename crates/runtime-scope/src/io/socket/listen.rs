//! The listen of a socket through the ring.

use ::core::ffi::c_int;
use ::core::marker::PhantomData;
use ::core::pin::Pin;
use ::core::task::Context;
use ::core::task::Poll;
use ::core::task::ready;
use ::gandr_runtime_uring::SlotDesc;
use ::gandr_runtime_uring::arg::Count;

use crate::completion::Completion;
use crate::error::RuntimeError;
use crate::scope::Scope;

/// The length of a listening socket's queue of connections that wait for an
/// accept.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Backlog(c_int);

impl Backlog
{
    /// The kernel's largest queue.
    pub const MAX: Self = Self(::libc::SOMAXCONN);
}

impl From<u16> for Backlog
{
    /// A queue of `len` connections.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn from(len: u16) -> Self
    {
        Self(c_int::from(len))
    }
}

/// The listen of a socket for connections.
#[non_exhaustive]
pub struct OpSocketListen<'tsk, 'env, 'fd>
{
    /// The completion of the listen.
    rsp: Completion<'tsk>,
    /// The borrows of the scope and of the socket, which the operation
    /// holds until its completion.
    phd: PhantomData<(&'tsk Scope<'tsk, 'env>, &'fd ::socket2::Socket)>,
}
impl<'tsk, 'env: 'tsk, 'fd> OpSocketListen<'tsk, 'env, 'fd>
{
    /// The listen of `socket` with a queue of `backlog` in `scope`.
    ///
    /// # Specification
    ///
    /// trivial.
    pub(crate) fn new(
        scope: &'tsk Scope<'tsk, 'env>,
        socket: &'fd ::socket2::Socket,
        backlog: Backlog,
    ) -> Self
    {
        let rsp = scope.request(|sqe| {
            // SAFETY: the operation holds `socket` until its completion.
            unsafe {
                sqe.prep_listen(SlotDesc::Desc(socket), Count(backlog.0));
            }
        });

        Self {
            rsp,
            phd: PhantomData,
        }
    }
}
impl Future for OpSocketListen<'_, '_, '_>
{
    type Output = Result<(), RuntimeError>;

    /// The listen's outcome, once the kernel completes it.
    ///
    /// # Specification
    ///
    /// - ensures: on `Ok`, the socket listens.
    /// - fails: the kernel's error when it refuses the listen, and the
    ///   completion's refusal.
    /// - panics: none.
    /// - executable: none — the socket's state is the kernel's, and the call
    ///   holds nothing to check it against.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — a bound Unix socket listens, and a client then
    ///   connects to it.
    /// - witness: `io::socket::test::socket::listen`
    /// - witness: `io::socket::test::socket::accept`
    fn poll(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Self::Output>
    {
        let this = self.get_mut();
        let cqe = ready!(Pin::new(&mut this.rsp).poll(cx))?;
        Poll::Ready(cqe.done())
    }
}
