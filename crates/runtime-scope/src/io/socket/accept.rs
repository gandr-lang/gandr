use ::core::pin::Pin;
use ::core::task::Context;
use ::core::task::Poll;
use ::core::task::ready;
use ::socket2::SockAddr;
use ::socket2::SockAddrStorage;
use ::socket2::socklen_t;
use ::std::os::fd::AsRawFd as _;
use ::std::os::fd::BorrowedFd;
use ::std::os::fd::FromRawFd as _;

use crate::completion::Completion;
use crate::io::socket::Socket;
use crate::scope::Scope;

::pin_project_lite::pin_project! {
#[non_exhaustive]
pub struct OpSocketAccept<'tsk, 'env: 'tsk, 'fd> {
    scope: &'tsk Scope<'tsk, 'env>,
    #[pin]
    rsp: Completion<'tsk>,
    fd: BorrowedFd<'fd>,
    addr: Pin<Box<(SockAddrStorage, socklen_t)>>,
}
}
impl<'tsk, 'env: 'tsk, 'fd> OpSocketAccept<'tsk, 'env, 'fd>
{
    pub(crate) fn new(
        scope: &'tsk Scope<'tsk, 'env>,
        fd: BorrowedFd<'fd>,
    ) -> Self
    {
        #[expect(clippy::as_conversions, reason = "size_of")]
        #[expect(clippy::cast_possible_truncation, reason = "size_of")]
        const STORAGE_SIZE: socklen_t = size_of::<SockAddrStorage>() as u32;

        let mut addr = Box::new((SockAddrStorage::zeroed(), STORAGE_SIZE));

        let op = {
            let fd = ::io_uring::types::Fd(fd.as_raw_fd());
            let addrlen = &raw mut addr.1;
            let addr = (&raw mut addr.0).cast();
            ::io_uring::opcode::Accept::new(fd, addr, addrlen)
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
impl<'tsk, 'env> Future for OpSocketAccept<'tsk, 'env, '_>
{
    type Output = ::anyhow::Result<(Socket<'tsk, 'env>, SockAddr)>;

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

        let socket = Socket {
            scope: this.scope,
            // SAFETY:
            inner: unsafe { ::socket2::Socket::from_raw_fd(cqe.result()) },
        };

        let storage = ::core::mem::replace(&mut this.addr.0, SockAddrStorage::zeroed());
        let len = this.addr.1;
        // SAFETY:
        let addr = unsafe { SockAddr::new(storage, len) };

        Poll::Ready(Ok((socket, addr)))
    }
}
