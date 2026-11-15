use ::anyhow::anyhow;
use ::core::marker::PhantomData;
use ::core::pin::Pin;
use ::core::pin::pin;
use ::core::task::Context;
use ::core::task::Poll;
use ::core::task::ready;

/// The kernel's completion of one operation, copied out of the ring.
pub struct Cqe
{
    res: i32,
    flags: u32,
}

impl Cqe
{
    pub(crate) const fn new(
        res: i32,
        flags: u32,
    ) -> Self
    {
        Self { res, flags }
    }

    pub const fn result(&self) -> i32
    {
        self.res
    }

    pub const fn flags(&self) -> u32
    {
        self.flags
    }
}

pub struct Completion<'tsk>
{
    cqe: Option<::oneshot::Receiver<Cqe>>,
    phd_tsk: PhantomData<&'tsk mut &'tsk ()>,
}

impl Completion<'_>
{
    pub(crate) const fn new(cqe: ::oneshot::Receiver<Cqe>) -> Self
    {
        let cqe = Some(cqe);
        Completion {
            cqe,
            phd_tsk: PhantomData,
        }
    }

    /// The completion of a request that found the submission queue full.
    pub(crate) const fn full() -> Self
    {
        Completion {
            cqe: None,
            phd_tsk: PhantomData,
        }
    }
}

impl Future for Completion<'_>
{
    type Output = ::anyhow::Result<Cqe>;

    fn poll(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Self::Output>
    {
        let this = self.get_mut();
        let Some(cqe) = this.cqe.as_mut()
        else {
            return Poll::Ready(Err(anyhow!("submission queue full")));
        };
        let cqe = pin!(cqe);
        let cqe = ready!(cqe.poll(cx)).map_err(|_err| anyhow!("value sender disconnected"))?;
        Poll::Ready(Ok(cqe))
    }
}
