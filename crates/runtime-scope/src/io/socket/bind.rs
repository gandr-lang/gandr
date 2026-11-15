use ::core::pin::Pin;
use ::core::task::Context;
use ::core::task::Poll;
use ::core::task::ready;
use ::gandr_runtime_uring::SlotDesc;
use ::socket2::SockAddr;

use crate::completion::Completion;
use crate::scope::Scope;

::pin_project_lite::pin_project! {
#[non_exhaustive]
pub struct OpSocketBind<'tsk, 'env: 'tsk, 'fd> {
    scope: &'tsk Scope<'tsk, 'env>,
    #[pin]
    rsp: Completion<'tsk>,
    socket: &'fd ::socket2::Socket,
    addr: Pin<Box<SockAddr>>,
}
}
impl<'tsk, 'env: 'tsk, 'fd> OpSocketBind<'tsk, 'env, 'fd>
{
    pub(crate) fn new(
        scope: &'tsk Scope<'tsk, 'env>,
        socket: &'fd ::socket2::Socket,
        addr: SockAddr,
    ) -> Self
    {
        let addr = Box::pin(addr);
        let rsp = scope.request(|sqe| {
            // SAFETY: the operation holds `socket` and the boxed `addr` until
            // its completion.
            unsafe { sqe.prep_bind(SlotDesc::Desc(socket), &addr) };
        });

        Self {
            scope,
            rsp,
            socket,
            addr,
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
