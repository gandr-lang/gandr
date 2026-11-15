use ::anyhow::anyhow;
use ::core::marker::PhantomData;
use ::core::pin::Pin;
use ::core::pin::pin;
use ::core::task::Context;
use ::core::task::Poll;
use ::core::task::ready;

use crate::submission::Submission;

enum State
{
    Submitting,
    Completing,
}

::pin_project_lite::pin_project! {
pub struct Completion<'tsk> {
    #[pin]
    sqe: ::kanal::SendFuture<'tsk, Submission>,
    cqe: ::oneshot::Receiver<::io_uring::cqueue::Entry>,
    state: State,
}
}

impl<'scope> Completion<'scope>
{
    pub(crate) fn new(
        sqe: ::kanal::SendFuture<'scope, Submission>,
        cqe: ::oneshot::Receiver<::io_uring::cqueue::Entry>,
    ) -> Self
    {
        let state = State::Submitting;
        Completion { sqe, cqe, state }
    }
}

impl Future for Completion<'_>
{
    type Output = ::anyhow::Result<::io_uring::cqueue::Entry>;

    fn poll(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Self::Output>
    {
        let mut this = self.project();
        match *this.state {
            State::Submitting => {
                ready!(this.sqe.poll(cx))?;
                *this.state = State::Completing;
                Poll::Pending
            },
            State::Completing => {
                let cqe = pin!(this.cqe);
                let cqe =
                    ready!(cqe.poll(cx)).map_err(|_err| anyhow!("value sender disconnected"))?;
                Poll::Ready(Ok(cqe))
            },
        }
    }
}
