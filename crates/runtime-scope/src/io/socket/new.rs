//! The creation of a socket through the ring.

use ::core::pin::Pin;
use ::core::task::Context;
use ::core::task::Poll;
use ::core::task::ready;
use ::socket2::Domain;
use ::socket2::Protocol;
use ::socket2::Type;

use crate::completion::Completion;
use crate::error::RuntimeError;
use crate::io::socket::Socket;
use crate::scope::Scope;

/// The creation of a socket: its completion gives the socket, a socket of
/// the scope.
#[non_exhaustive]
pub struct OpSocketNew<'tsk, 'env>
{
    /// The scope of the socket.
    scope: &'tsk Scope<'tsk, 'env>,
    /// The completion of the creation.
    cqe: Completion<'tsk>,
}
impl<'tsk, 'env: 'tsk> OpSocketNew<'tsk, 'env>
{
    /// The creation of a socket of `domain`, `ty` and `protocol` in `scope`.
    ///
    /// # Specification
    ///
    /// trivial.
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

    /// The socket, once the kernel creates it.
    ///
    /// # Specification
    ///
    /// - provides: the new socket, which owns its descriptor.
    /// - fails: the kernel's error when it refuses the socket, and the
    ///   completion's refusal.
    /// - panics: none.
    /// - executable: none — the descriptor is the kernel's, and the call holds
    ///   nothing to check it against.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — the kernel creates a socket of the Unix domain.
    /// - witness: `io::socket::test::socket::new`
    fn poll(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Self::Output>
    {
        let this = self.get_mut();
        let cqe = ready!(Pin::new(&mut this.cqe).poll(cx))?;
        // SAFETY: a socket's creation makes a descriptor when it does not
        // fail, and nothing else owns it.
        let fd = unsafe { cqe.descriptor() }?;

        Poll::Ready(Ok(Socket {
            scope: this.scope,
            inner: ::socket2::Socket::from(fd),
        }))
    }
}
