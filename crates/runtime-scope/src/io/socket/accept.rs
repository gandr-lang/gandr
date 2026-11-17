//! The accept of a connection on a listening socket through the ring.

use ::core::marker::PhantomData;
use ::core::pin::Pin;
use ::core::ptr::NonNull;
use ::core::task::Context;
use ::core::task::Poll;
use ::core::task::ready;
use ::gandr_runtime_uring::SlotDesc;
use ::gandr_runtime_uring::arg::Len;
use ::socket2::SockAddr;
use ::socket2::SockAddrStorage;
use ::socket2::socklen_t;

use crate::completion::Completion;
use crate::error::RuntimeError;
use crate::io::socket::Socket;
use crate::scope::Scope;

/// The storage of an accepted peer's address, lent for the scope's life:
/// the kernel writes it when a connection arrives.
pub struct PeerAddr
{
    /// The address's bytes.
    storage: SockAddrStorage,
    /// The address's length: the storage's size before the accept, and the
    /// length that the kernel writes after it.
    len: socklen_t,
}

impl PeerAddr
{
    /// Empty storage, with room for any address.
    ///
    /// # Specification
    ///
    /// trivial.
    #[must_use]
    #[inline]
    pub fn new() -> Self
    {
        #[expect(
            clippy::as_conversions,
            reason = "a const holds no TryFrom, and the storage's size is 128 bytes"
        )]
        #[expect(
            clippy::cast_possible_truncation,
            reason = "a const holds no TryFrom, and the storage's size is 128 bytes"
        )]
        const STORAGE_SIZE: socklen_t = size_of::<SockAddrStorage>() as u32;

        Self {
            storage: SockAddrStorage::zeroed(),
            len: STORAGE_SIZE,
        }
    }
}

impl Default for PeerAddr
{
    /// Empty storage, with room for any address.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::new()
    }
}

/// The accept of a connection, whose peer's address the kernel writes into
/// storage that the caller lends for the scope's life.
#[non_exhaustive]
pub struct OpSocketAccept<'tsk, 'env, 'fd>
{
    /// The scope of the socket.
    scope: &'tsk Scope<'tsk, 'env>,
    /// The completion of the accept.
    rsp: Completion<'tsk>,
    /// The peer's storage, which the kernel writes until the completion.
    peer: NonNull<PeerAddr>,
    /// The borrows of the peer's storage for the scope's life and of the
    /// listening socket, which the operation holds until its completion.
    phd: PhantomData<(&'tsk mut PeerAddr, &'fd ::socket2::Socket)>,
}
impl<'tsk, 'env: 'tsk, 'fd> OpSocketAccept<'tsk, 'env, 'fd>
{
    /// The accept of a connection on `socket` in `scope`, with the peer's
    /// address written into `peer`.
    ///
    /// # Specification
    ///
    /// trivial.
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
                    Len(&mut peer.len),
                    flags,
                    None,
                );
            }
        });

        Self {
            scope,
            rsp,
            peer: NonNull::from(peer),
            phd: PhantomData,
        }
    }
}
impl<'tsk, 'env> Future for OpSocketAccept<'tsk, 'env, '_>
{
    type Output = Result<(Socket<'tsk, 'env>, SockAddr), RuntimeError>;

    /// The accepted connection and its peer's address, once the kernel
    /// completes the accept.
    ///
    /// # Specification
    ///
    /// - provides: the connection as a socket of the scope, and the peer's
    ///   address.
    /// - fails: the kernel's error when it refuses the accept, and the
    ///   completion's refusal.
    /// - panics: none.
    /// - executable: none — the connection is the kernel's, and the call holds
    ///   nothing to check it against.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — a client connects to a listening Unix socket, and the
    ///   accept gives its connection.
    /// - witness: `io::socket::test::socket::accept`
    fn poll(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Self::Output>
    {
        let this = self.get_mut();
        let cqe = ready!(Pin::new(&mut this.rsp).poll(cx))?;
        // SAFETY: an accept makes a descriptor when it does not fail, and
        // nothing else owns it.
        let fd = unsafe { cqe.descriptor() }?;
        let socket = Socket {
            scope: this.scope,
            inner: ::socket2::Socket::from(fd),
        };

        // SAFETY: the kernel completed the accept, so it writes the peer's
        // storage no more, and the borrow `'tsk` lends the storage to this
        // operation alone.
        let peer = unsafe { this.peer.as_mut() };
        let storage = ::core::mem::replace(&mut peer.storage, SockAddrStorage::zeroed());
        let len = peer.len;
        // SAFETY: the kernel wrote an address of `len` bytes into the
        // storage.
        let addr = unsafe { SockAddr::new(storage, len) };

        Poll::Ready(Ok((socket, addr)))
    }
}
