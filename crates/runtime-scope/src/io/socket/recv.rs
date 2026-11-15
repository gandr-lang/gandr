use ::core::pin::Pin;
use ::core::task::Context;
use ::core::task::Poll;
use ::core::task::ready;
use ::std::os::fd::AsRawFd as _;

use crate::completion::Completion;
use crate::error::RuntimeError;
use crate::scope::Scope;

::pin_project_lite::pin_project! {
/// A receive into a buffer that the scope's caller lends for the scope's
/// life. The borrow `'tsk` holds the buffer until the scope ends, so no
/// caller reads it while the kernel writes it; the completion gives it back
/// with the count of bytes received.
#[non_exhaustive]
pub struct OpSocketRecv<'tsk, 'env: 'tsk, 'fd> {
    scope: &'tsk Scope<'tsk, 'env>,
    #[pin]
    rsp: Completion<'tsk>,
    socket: &'fd ::socket2::Socket,
    buf: Option<&'tsk mut [u8]>,
}
}
impl<'tsk, 'env: 'tsk, 'fd> OpSocketRecv<'tsk, 'env, 'fd>
{
    pub(crate) fn new(
        scope: &'tsk Scope<'tsk, 'env>,
        socket: &'fd ::socket2::Socket,
        buf: &'tsk mut [u8],
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
                sqe.prep_recv(fd, ptr, len, 0);
            }
        });

        Self {
            scope,
            rsp,
            socket,
            buf: Some(buf),
        }
    }
}
impl<'tsk> Future for OpSocketRecv<'tsk, '_, '_>
{
    type Output = Result<(usize, &'tsk mut [u8]), RuntimeError>;

    fn poll(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Self::Output>
    {
        let this = self.as_mut().project();
        let cqe = ready!(this.rsp.poll(cx))?;
        let buf = this.buf.take().ok_or(RuntimeError::Read)?;

        let Ok(len) = usize::try_from(cqe.result())
        else {
            return Poll::Ready(Err(RuntimeError::completion(cqe.result())));
        };

        Poll::Ready(Ok((len, buf)))
    }
}
