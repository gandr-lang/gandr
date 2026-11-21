//! The receive of a socket's bytes into a lent buffer through the ring.

use ::core::marker::PhantomData;
use ::core::pin::Pin;
use ::core::task::Context;
use ::core::task::Poll;
use ::core::task::ready;
use ::gandr_runtime_uring::arg::Fd;
use ::gandr_runtime_uring::arg::Flags;
use ::gandr_runtime_uring::arg::Len;
use ::std::os::fd::AsRawFd as _;

use crate::completion::Completion;
use crate::error::RuntimeError;
use crate::io::buf::Buf;
use crate::scope::Scope;

/// A receive into a buffer that the scope's caller lends for the scope's
/// life. The borrow `'tsk` holds the buffer until the scope ends, so no
/// caller reads it while the kernel writes it; the completion gives back
/// the bytes received.
#[non_exhaustive]
pub struct OpSocketRecv<'tsk, 'env, 'fd>
{
    /// The completion of the receive.
    rsp: Completion<'tsk>,
    /// The buffer, until the completion gives it back.
    buf: Option<Buf<'tsk>>,
    /// The borrows of the scope and of the socket, which the operation
    /// holds until its completion.
    phd: PhantomData<(&'tsk Scope<'tsk, 'env>, &'fd ::socket2::Socket)>,
}
impl<'tsk, 'env: 'tsk, 'fd> OpSocketRecv<'tsk, 'env, 'fd>
{
    /// The receive of `socket`'s bytes into `buf` in `scope`.
    ///
    /// # Specification
    ///
    /// trivial.
    pub(crate) fn new(
        scope: &'tsk Scope<'tsk, 'env>,
        socket: &'fd ::socket2::Socket,
        mut buf: Buf<'tsk>,
    ) -> Self
    {
        let rsp = scope.request(|sqe| {
            let fd = socket.as_raw_fd();
            let len = buf.len();
            let ptr = buf.as_mut_ptr().cast();
            // SAFETY: the buffer is borrowed for the scope's life, and the
            // scope's end drains the receive before the borrow ends; the
            // operation holds `socket` until its completion.
            unsafe {
                sqe.prep_recv(Fd(fd), ptr, Len(len), Flags(0_i32));
            }
        });

        Self {
            rsp,
            buf: Some(buf),
            phd: PhantomData,
        }
    }
}
impl<'tsk> Future for OpSocketRecv<'tsk, '_, '_>
{
    type Output = Result<Buf<'tsk>, RuntimeError>;

    /// The bytes received, once the kernel completes the receive.
    ///
    /// # Specification
    ///
    /// - provides: the buffer's prefix that the kernel wrote.
    /// - fails: the kernel's error when it refuses the receive, `Read` when the
    ///   receive already gave the buffer back, `Overrun` when the kernel's
    ///   count passes the buffer, and the completion's refusal.
    /// - panics: none.
    /// - executable: none — the bytes are the peer's, and the call holds
    ///   nothing to check them against.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — a receive of the bytes `ping` into a buffer of eight
    ///   gives the four bytes.
    /// - witness: `io::socket::test::socket::recv`
    fn poll(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Self::Output>
    {
        let this = self.get_mut();
        let cqe = ready!(Pin::new(&mut this.rsp).poll(cx))?;
        let buf = this.buf.take().ok_or(RuntimeError::Read)?;
        let count = cqe.count()?;
        Poll::Ready(buf.prefix(count).ok_or(RuntimeError::Overrun))
    }
}
