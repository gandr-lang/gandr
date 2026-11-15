use ::core::marker::PhantomData;
use ::core::pin::Pin;
use ::core::ptr::NonNull;
use ::core::task::Context;
use ::core::task::Poll;
use ::core::task::ready;
use ::gandr_runtime_uring::SlotDesc;
use ::socket2::SockAddr;
use ::socket2::SockAddrStorage;
use ::socket2::socklen_t;
use ::std::os::fd::FromRawFd as _;

use crate::completion::Completion;
use crate::error::RuntimeError;
use crate::io::socket::Socket;
use crate::scope::Scope;

/// The storage of an accepted peer's address, lent for the scope's life:
/// the kernel writes it when a connection arrives.
pub struct PeerAddr
{
    storage: SockAddrStorage,
    len: socklen_t,
}

impl PeerAddr
{
    /// Empty storage, with room for any address.
    #[must_use]
    #[inline]
    pub fn new() -> Self
    {
        #[expect(clippy::as_conversions, reason = "size_of")]
        #[expect(clippy::cast_possible_truncation, reason = "size_of")]
        const STORAGE_SIZE: socklen_t = size_of::<SockAddrStorage>() as u32;

        Self {
            storage: SockAddrStorage::zeroed(),
            len: STORAGE_SIZE,
        }
    }
}

impl Default for PeerAddr
{
    #[inline]
    fn default() -> Self
    {
        Self::new()
    }
}

::pin_project_lite::pin_project! {
#[non_exhaustive]
pub struct OpSocketAccept<'tsk, 'env: 'tsk, 'fd> {
    scope: &'tsk Scope<'tsk, 'env>,
    #[pin]
    rsp: Completion<'tsk>,
    socket: &'fd ::socket2::Socket,
    peer: NonNull<PeerAddr>,
    phd_peer: PhantomData<&'tsk mut PeerAddr>,
}
}
impl<'tsk, 'env: 'tsk, 'fd> OpSocketAccept<'tsk, 'env, 'fd>
{
    pub(crate) fn new(
        scope: &'tsk Scope<'tsk, 'env>,
        socket: &'fd ::socket2::Socket,
        peer: &'tsk mut PeerAddr,
    ) -> Self
    {
        let rsp = scope.request(|sqe| {
            let flags = ::rustix::net::SocketFlags::empty();
            // SAFETY: the peer's storage is borrowed for the scope's life, and
            // the scope's end drains the accept before the borrow ends; the
            // operation holds `socket` until its completion.
            unsafe {
                sqe.prep_accept(
                    SlotDesc::Desc(socket),
                    &mut peer.storage,
                    &mut peer.len,
                    flags,
                    None,
                );
            }
        });

        Self {
            scope,
            rsp,
            socket,
            peer: NonNull::from(peer),
            phd_peer: PhantomData,
        }
    }
}
impl<'tsk, 'env> Future for OpSocketAccept<'tsk, 'env, '_>
{
    type Output = Result<(Socket<'tsk, 'env>, SockAddr), RuntimeError>;

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

        let socket = Socket {
            scope: this.scope,
            // SAFETY:
            inner: unsafe { ::socket2::Socket::from_raw_fd(cqe.result()) },
        };

        // SAFETY: the kernel completed the accept, so it writes the peer's
        // storage no more, and the borrow `'tsk` lends the storage to this
        // operation alone.
        let peer = unsafe { this.peer.as_mut() };
        let storage = ::core::mem::replace(&mut peer.storage, SockAddrStorage::zeroed());
        let len = peer.len;
        // SAFETY:
        let addr = unsafe { SockAddr::new(storage, len) };

        Poll::Ready(Ok((socket, addr)))
    }
}
