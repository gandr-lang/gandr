use ::core::pin::Pin;
use ::core::task::Context;
use ::core::task::Poll;
use ::core::task::ready;
use ::socket2::SockAddr;
use ::socket2::SockAddrStorage;
use ::std::os::fd::AsRawFd as _;
use ::std::os::fd::BorrowedFd;

use crate::completion::Completion;
use crate::scope::Scope;

::pin_project_lite::pin_project! {
#[non_exhaustive]
pub struct OpSocketBind<'tsk, 'env: 'tsk, 'fd> {
    scope: &'tsk Scope<'tsk, 'env>,
    #[pin]
    rsp: Completion<'tsk>,
    fd: BorrowedFd<'fd>,
    addr: Pin<Box<SockAddrStorage>>,
}
}
impl<'tsk, 'env: 'tsk, 'fd> OpSocketBind<'tsk, 'env, 'fd>
{
    pub(crate) fn new(
        scope: &'tsk Scope<'tsk, 'env>,
        fd: BorrowedFd<'fd>,
        addr: SockAddr,
    ) -> Self
    {
        let addrlen = addr.len();
        let mut addr = Box::new(addr.as_storage());
        let op = {
            let fd = ::io_uring::types::Fd(fd.as_raw_fd());
            // SAFETY:
            let addr = unsafe { addr.view_as::<::libc::sockaddr>() };
            ::io_uring::opcode::Bind::new(fd, addr, addrlen)
        };
        let sqe = op.build();
        let rsp = scope.request(sqe);

        Self {
            scope,
            rsp,
            fd,
            addr: Pin::new(addr),
        }
    }
}
impl Future for OpSocketBind<'_, '_, '_>
{
    type Output = ::anyhow::Result<()>;

    fn poll(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Self::Output>
    {
        let this = self.as_mut().project();
        let cqe = ready!(this.rsp.poll(cx))?;

        if cqe.result().is_negative() {
            let code = cqe.result().abs();
            let err = ::std::io::Error::from_raw_os_error(code);
            return Poll::Ready(Err(err.into()));
        }

        Poll::Ready(Ok(()))
    }
}
