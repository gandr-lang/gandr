use ::core::pin::Pin;
use ::core::task::Context;
use ::core::task::Poll;
use ::core::task::ready;
use ::gandr_runtime_uring::SlotDesc;
use ::socket2::SockAddr;

use crate::completion::Completion;
use crate::error::RuntimeError;
use crate::scope::Scope;

::pin_project_lite::pin_project! {
#[non_exhaustive]
pub struct OpSocketBind<'tsk, 'env: 'tsk, 'fd> {
    scope: &'tsk Scope<'tsk, 'env>,
    #[pin]
    rsp: Completion<'tsk>,
    socket: &'fd ::socket2::Socket,
    addr: &'tsk SockAddr,
}
}
impl<'tsk, 'env: 'tsk, 'fd> OpSocketBind<'tsk, 'env, 'fd>
{
    pub(crate) fn new(
        scope: &'tsk Scope<'tsk, 'env>,
        socket: &'fd ::socket2::Socket,
        addr: &'tsk SockAddr,
    ) -> Self
    {
        let rsp = scope.request(|sqe| {
            // SAFETY: the address is borrowed for the scope's life, and the
            // scope's end drains the bind before the borrow ends; the
            // operation holds `socket` until its completion.
            unsafe {
                sqe.prep_bind(SlotDesc::Desc(socket), addr);
            }
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
    type Output = Result<(), RuntimeError>;

    fn poll(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Self::Output>
    {
        let this = self.as_mut().project();
        let cqe = ready!(this.rsp.poll(cx))?;

        if cqe.result().is_negative() {
            return Poll::Ready(Err(RuntimeError::completion(cqe.result())));
        }

        Poll::Ready(Ok(()))
    }
}
