use ::core::pin::Pin;
use ::core::task::Context;
use ::core::task::Poll;
use ::core::task::ready;
use ::gandr_runtime_uring::SlotDesc;

use crate::completion::Completion;
use crate::scope::Scope;

::pin_project_lite::pin_project! {
#[non_exhaustive]
pub struct OpSocketListen<'tsk, 'env: 'tsk, 'fd> {
    scope: &'tsk Scope<'tsk, 'env>,
    #[pin]
    rsp: Completion<'tsk>,
    socket: &'fd ::socket2::Socket,
}
}
impl<'tsk, 'env: 'tsk, 'fd> OpSocketListen<'tsk, 'env, 'fd>
{
    pub(crate) fn new(
        scope: &'tsk Scope<'tsk, 'env>,
        socket: &'fd ::socket2::Socket,
        backlog: ::core::ffi::c_int,
    ) -> Self
    {
        let rsp = scope.request(|sqe| {
            // SAFETY: the operation holds `socket` until its completion.
            unsafe { sqe.prep_listen(SlotDesc::Desc(socket), backlog) };
        });

        Self { scope, rsp, socket }
    }
}
impl Future for OpSocketListen<'_, '_, '_>
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
