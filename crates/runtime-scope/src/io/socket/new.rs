use ::core::pin::Pin;
use ::core::task::Context;
use ::core::task::Poll;
use ::core::task::ready;
use ::socket2::Domain;
use ::socket2::Protocol;
use ::socket2::Type;
use ::std::os::fd::FromRawFd as _;

use crate::completion::Completion;
use crate::error::RuntimeError;
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
        let cqe = scope.request(|sqe| {
            let flags = ::rustix::net::SocketFlags::empty();
            // SAFETY: a socket's creation reads no pointer and names no
            // descriptor.
            unsafe {
                sqe.prep_socket(domain, ty, protocol, flags, None);
            }
        });

        Self { scope, cqe }
    }
}
impl<'tsk, 'env: 'tsk> Future for OpSocketNew<'tsk, 'env>
{
    type Output = Result<Socket<'tsk, 'env>, RuntimeError>;

    fn poll(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Self::Output>
    {
        let this = self.as_mut().project();
        let cqe = ready!(this.cqe.poll(cx))?;

        if cqe.result().is_negative() {
            return Poll::Ready(Err(RuntimeError::completion(cqe.result())));
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
