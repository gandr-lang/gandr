//! The bind of a socket to an address through the ring.

use ::core::marker::PhantomData;
use ::core::pin::Pin;
use ::core::task::Context;
use ::core::task::Poll;
use ::core::task::ready;
use ::gandr_runtime_uring::SlotDesc;
use ::socket2::SockAddr;

use crate::completion::Completion;
use crate::error::RuntimeError;
use crate::scope::Scope;

/// The bind of a socket to an address that the caller lends for the
/// scope's life.
#[non_exhaustive]
pub struct OpSocketBind<'tsk, 'env, 'fd>
{
    /// The completion of the bind.
    rsp: Completion<'tsk>,
    /// The borrows of the scope, of the socket and of the address, which
    /// the operation holds until its completion.
    phd: PhantomData<(
        &'tsk Scope<'tsk, 'env>,
        &'fd ::socket2::Socket,
        &'tsk SockAddr,
    )>,
}
impl<'tsk, 'env: 'tsk, 'fd> OpSocketBind<'tsk, 'env, 'fd>
{
    /// The bind of `socket` to `addr` in `scope`.
    ///
    /// # Specification
    ///
    /// trivial.
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
            rsp,
            phd: PhantomData,
        }
    }
}
impl Future for OpSocketBind<'_, '_, '_>
{
    type Output = Result<(), RuntimeError>;

    /// The bind's outcome, once the kernel completes it.
    ///
    /// # Specification
    ///
    /// - ensures: on `Ok`, the socket has the address.
    /// - fails: the kernel's error when it refuses the bind, and the
    ///   completion's refusal.
    /// - panics: none.
    /// - executable: none — the socket's address is the kernel's, and the call
    ///   holds nothing to check it against.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — a bind to a Unix path makes the path.
    /// - witness: `io::socket::test::socket::bind`
    fn poll(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Self::Output>
    {
        let this = self.get_mut();
        let cqe = ready!(Pin::new(&mut this.rsp).poll(cx))?;
        Poll::Ready(cqe.done())
    }
}
