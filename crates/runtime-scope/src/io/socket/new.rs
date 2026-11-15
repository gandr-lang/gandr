use ::core::pin::Pin;
use ::core::task::Context;
use ::core::task::Poll;
use ::core::task::ready;
use ::socket2::Domain;
use ::socket2::Protocol;
use ::socket2::Type;
use ::std::os::fd::FromRawFd as _;

use crate::completion::Completion;
use crate::io::socket::Socket;
use crate::scope::Scope;

::pin_project_lite::pin_project! {
#[non_exhaustive]
pub struct OpSocketNew<'tsk, 'env: 'tsk> {
    scope: &'tsk Scope<'tsk, 'env>,
    #[pin]
    cqe: Completion<'tsk>,
}
}
impl<'tsk, 'env: 'tsk> OpSocketNew<'tsk, 'env>
{
    pub(crate) fn new(
        scope: &'tsk Scope<'tsk, 'env>,
        domain: Domain,
        ty: Type,
        protocol: Option<Protocol>,
    ) -> Self
    {
        let domain = i32::from(domain);
        let ty = i32::from(ty);
        let protocol = protocol.map_or(0i32, i32::from);

        let op = ::io_uring::opcode::Socket::new(domain, ty, protocol);
        let sqe = op.build();
        let cqe = scope.request(sqe);

        Self { scope, cqe }
    }
}
impl<'tsk, 'env: 'tsk> Future for OpSocketNew<'tsk, 'env>
{
    type Output = ::anyhow::Result<Socket<'tsk, 'env>>;

    fn poll(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Self::Output>
    {
        let this = self.as_mut().project();
        let cqe = ready!(this.cqe.poll(cx))?;

        if cqe.result().is_negative() {
            let code = cqe.result().abs();
            let err = ::std::io::Error::from_raw_os_error(code);
            return Poll::Ready(Err(err.into()));
        }

        let fd = cqe.result();
        // SAFETY: trustme
        let inner = unsafe { ::socket2::Socket::from_raw_fd(fd) };

        Poll::Ready(Ok(Socket {
            scope: self.scope,
            inner,
        }))
    }
}
