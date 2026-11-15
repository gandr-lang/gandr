use ::core::marker::PhantomData;
use ::core::pin::Pin;
use ::core::task::Context;
use ::core::task::Poll;

use crate::error::RuntimeError;
use crate::submission::Table;

/// The kernel's completion of one operation, copied out of the ring.
#[derive(Clone, Copy)]
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

    pub const fn result(self) -> i32
    {
        self.res
    }

    pub const fn flags(self) -> u32
    {
        self.flags
    }
}

/// Where a completion stands.
enum State
{
    /// The table had no free slot for the request.
    Full,
    /// The operation holds slot `key`.
    Waiting(usize),
    /// The completion gave its result.
    Read,
}

pub struct Completion<'tsk>
{
    table: &'tsk Table,
    state: State,
    phd_tsk: PhantomData<&'tsk mut &'tsk ()>,
}

impl<'tsk> Completion<'tsk>
{
    pub(crate) const fn new(
        table: &'tsk Table,
        key: usize,
    ) -> Self
    {
        Completion {
            table,
            state: State::Waiting(key),
            phd_tsk: PhantomData,
        }
    }

    /// The completion of a request that found no free slot.
    pub(crate) const fn full(table: &'tsk Table) -> Self
    {
        Completion {
            table,
            state: State::Full,
            phd_tsk: PhantomData,
        }
    }
}

impl Drop for Completion<'_>
{
    fn drop(&mut self)
    {
        if let State::Waiting(key) = self.state {
            self.table.abandon(key);
        }
    }
}

impl Future for Completion<'_>
{
    type Output = Result<Cqe, RuntimeError>;

    fn poll(
        self: Pin<&mut Self>,
        _cx: &mut Context<'_>,
    ) -> Poll<Self::Output>
    {
        let this = self.get_mut();
        match this.state {
            State::Full => Poll::Ready(Err(RuntimeError::Full)),
            State::Read => Poll::Ready(Err(RuntimeError::Read)),
            State::Waiting(key) => {
                let Some(cqe) = this.table.read(key)
                else {
                    return Poll::Pending;
                };
                this.state = State::Read;
                Poll::Ready(Ok(cqe))
            },
        }
    }
}
