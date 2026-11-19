//! A socket of the scope, whose operations go through the ring.

mod accept;
mod bind;
mod listen;
mod new;
mod recv;

use ::socket2::Domain;
use ::socket2::Protocol;
use ::socket2::SockAddr;
use ::socket2::Type;

use crate::io::buf::Buf;
use crate::io::socket::accept::OpSocketAccept;
pub use crate::io::socket::accept::PeerAddr;
use crate::io::socket::bind::OpSocketBind;
pub use crate::io::socket::listen::Backlog;
use crate::io::socket::listen::OpSocketListen;
use crate::io::socket::new::OpSocketNew;
use crate::io::socket::recv::OpSocketRecv;
use crate::scope::Scope;

/// A socket of the scope: its descriptor, and the scope whose ring takes
/// its operations.
#[non_exhaustive]
pub struct Socket<'tsk, 'env>
{
    /// The scope whose ring takes the socket's operations.
    scope: &'tsk Scope<'tsk, 'env>,
    /// The socket's descriptor.
    inner: ::socket2::Socket,
}

impl<'tsk, 'env: 'tsk> Socket<'tsk, 'env>
{
    /// The creation of a socket of `domain`, `ty` and `protocol` in
    /// `scope`.
    ///
    /// # Specification
    ///
    /// trivial.
    #[expect(
        clippy::new_ret_no_self,
        reason = "the creation is an operation of the ring, so it gives a future of the socket"
    )]
    #[must_use]
    #[inline]
    pub fn new(
        scope: &'tsk Scope<'tsk, 'env>,
        domain: Domain,
        ty: Type,
        protocol: Option<Protocol>,
    ) -> OpSocketNew<'tsk, 'env>
    {
        OpSocketNew::new(scope, domain, ty, protocol)
    }

    /// A bind of the socket to `addr`, an address lent for the scope's life.
    ///
    /// # Specification
    ///
    /// trivial.
    #[must_use]
    #[inline]
    pub fn bind(
        &self,
        addr: &'tsk SockAddr,
    ) -> OpSocketBind<'tsk, 'env, '_>
    {
        let scope = self.scope;
        OpSocketBind::new(scope, &self.inner, addr)
    }

    /// A listen of the socket, with a queue of `backlog` connections.
    ///
    /// # Specification
    ///
    /// trivial.
    #[must_use]
    #[inline]
    pub fn listen(
        &self,
        backlog: Backlog,
    ) -> OpSocketListen<'tsk, 'env, '_>
    {
        let scope = self.scope;
        OpSocketListen::new(scope, &self.inner, backlog)
    }

    /// An accept of a connection, whose peer's address the kernel writes
    /// into `peer`, storage lent for the scope's life.
    ///
    /// # Specification
    ///
    /// trivial.
    #[must_use]
    #[inline]
    pub fn accept(
        &self,
        peer: &'tsk mut PeerAddr,
    ) -> OpSocketAccept<'tsk, 'env, '_>
    {
        let scope = self.scope;
        OpSocketAccept::new(scope, &self.inner, peer)
    }

    /// A receive of at most the length of `buf` into `buf`, a buffer lent
    /// for the scope's life; the completion gives back the bytes received.
    ///
    /// # Specification
    ///
    /// trivial.
    #[must_use]
    #[inline]
    pub fn recv(
        &self,
        buf: Buf<'tsk>,
    ) -> OpSocketRecv<'tsk, 'env, '_>
    {
        let scope = self.scope;
        OpSocketRecv::new(scope, &self.inner, buf)
    }
}

/// The socket's tests and their harness.
#[cfg(test)]
pub(crate) mod test
{
    use super::*;

    /// The harness of the socket's tests.
    pub mod harness
    {
        use super::*;

        /// The creation of a stream socket of the Unix domain in `scope`.
        ///
        /// # Specification
        ///
        /// trivial.
        pub fn new<'tsk, 'env>(scope: &'tsk Scope<'tsk, 'env>) -> OpSocketNew<'tsk, 'env>
        {
            let domain = Domain::UNIX;
            let ty = Type::STREAM;
            let protocol = None;
            Socket::new(scope, domain, ty, protocol)
        }

        /// The near end of a connected pair as a socket of `scope`.
        ///
        /// # Specification
        ///
        /// trivial.
        pub fn wrap<'tsk, 'env>(
            scope: &'tsk Scope<'tsk, 'env>,
            near: ::std::os::unix::net::UnixStream,
        ) -> Socket<'tsk, 'env>
        {
            let inner = ::socket2::Socket::from(::std::os::fd::OwnedFd::from(near));
            Socket { scope, inner }
        }

        /// A buffer of eight zero bytes, lent through the allocator of
        /// `region` for the region's life.
        ///
        /// # Specification
        ///
        /// trivial.
        ///
        /// # Cost
        ///
        /// - allocation: the buffer's bytes in the region, setup
        pub fn lend<'region>(
            region: &'region ::gandr_kernel_data::Region<'_, (), ::alloc::alloc::Global>
        ) -> Buf<'region>
        {
            let mut bytes = ::alloc::vec::Vec::with_capacity_in(8, region);
            bytes.resize(8, 0_u8);
            Buf::from(bytes.leak())
        }
    }

    /// The socket's tests.
    pub mod socket
    {
        use ::assert_fs::assert::PathAssert as _;
        use ::assert_fs::prelude::PathChild as _;
        use ::predicates::prelude::PredicateBooleanExt as _;

        use super::*;

        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring of the kernel, which Miri cannot run"
        )]
        fn new()
        {
            crate::test::harness::runtime::new()
                .run(async |scope| -> Result<(), crate::RuntimeError> {
                    let socket = crate::test::harness::io::socket::new(scope);
                    let socket = socket.await?;
                    drop(socket);
                    Ok(())
                })
                .unwrap()
                .unwrap();
        }

        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring of the kernel, which Miri cannot run"
        )]
        fn bind()
        {
            let temp = ::assert_fs::TempDir::new().unwrap();
            let path = temp.child("socket");
            let addr = ::socket2::SockAddr::unix(&path).unwrap();
            crate::test::harness::runtime::new()
                .run(async |scope| -> Result<(), crate::RuntimeError> {
                    let socket = crate::test::harness::io::socket::new(scope);
                    let socket = socket.await?;
                    path.assert(::predicates::path::exists().not());
                    socket.bind(&addr).await?;
                    path.assert(::predicates::path::exists());
                    Ok(())
                })
                .unwrap()
                .unwrap();
        }

        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring of the kernel, which Miri cannot run"
        )]
        fn listen()
        {
            let temp = ::assert_fs::TempDir::new().unwrap();
            let path = temp.child("socket");
            let addr = ::socket2::SockAddr::unix(&path).unwrap();
            crate::test::harness::runtime::new()
                .run(async |scope| -> Result<(), crate::RuntimeError> {
                    let socket = crate::test::harness::io::socket::new(scope);
                    let socket = socket.await?;
                    path.assert(::predicates::path::exists().not());
                    socket.bind(&addr).await?;
                    path.assert(::predicates::path::exists());
                    socket.listen(Backlog::MAX).await?;
                    Ok(())
                })
                .unwrap()
                .unwrap();
        }

        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring of the kernel, which Miri cannot run"
        )]
        fn accept()
        {
            let temp = ::assert_fs::TempDir::new().unwrap();
            let path = temp.child("socket");
            let connector = ::std::thread::spawn({
                let path = path.to_owned();
                move || loop {
                    if ::std::os::unix::net::UnixStream::connect(&path).is_ok() {
                        break;
                    }
                    ::core::hint::spin_loop();
                }
            });
            let addr = ::socket2::SockAddr::unix(&path).unwrap();
            let mut peer = PeerAddr::new();
            crate::test::harness::runtime::new()
                .run(async |scope| -> Result<(), crate::RuntimeError> {
                    let socket = crate::test::harness::io::socket::new(scope);
                    let socket = socket.await?;
                    socket.bind(&addr).await?;
                    socket.listen(Backlog::MAX).await?;
                    let (socket, sockaddr) = socket.accept(&mut peer).await?;
                    drop((socket, sockaddr));
                    Ok(())
                })
                .unwrap()
                .unwrap();
            connector.join().unwrap();
        }

        /// A scope that ends with an accept in flight cancels it, and the
        /// run returns only once the kernel completes the cancel and the
        /// accept. No client connects, so only the cancel ends the accept.
        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring of the kernel, which Miri cannot run"
        )]
        fn accept_in_flight()
        {
            let temp = ::assert_fs::TempDir::new().unwrap();
            let path = temp.child("socket");
            let addr = ::socket2::SockAddr::unix(&path).unwrap();
            let mut peer = PeerAddr::new();
            crate::test::harness::runtime::new()
                .run(async |scope| -> Result<(), crate::RuntimeError> {
                    let socket = crate::test::harness::io::socket::new(scope);
                    let socket = socket.await?;
                    socket.bind(&addr).await?;
                    socket.listen(Backlog::MAX).await?;
                    let accept = socket.accept(&mut peer);
                    drop(accept);
                    Ok(())
                })
                .unwrap()
                .unwrap();
        }

        /// A receive into a buffer that the region lends gives the bytes
        /// that the peer sent, and the buffer back.
        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring of the kernel, which Miri cannot run"
        )]
        fn recv()
        {
            let (near, mut far) = ::std::os::unix::net::UnixStream::pair().unwrap();
            ::std::io::Write::write_all(&mut far, b"ping").unwrap();
            let budget = ::gandr_kernel_data::Budget::from(4096_usize);
            ::gandr_kernel_data::scoped::<(), _, _>(budget, |region, _mint| {
                let buf = harness::lend(region);
                let got = crate::test::harness::runtime::new()
                    .run(async |scope| -> Result<Vec<u8>, crate::RuntimeError> {
                        let socket = harness::wrap(scope, near);
                        let got = socket.recv(buf).await?;
                        Ok(got.to_vec())
                    })
                    .unwrap()
                    .unwrap();
                assert_eq!(got.as_slice(), b"ping".as_slice());
            });
        }

        /// A scope that ends with a receive in flight cancels it before the
        /// run returns. So the bytes that the peer sends after the run stay
        /// in the socket, and the region's buffer keeps its zeros.
        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring of the kernel, which Miri cannot run"
        )]
        fn recv_in_flight()
        {
            let (near, mut far) = ::std::os::unix::net::UnixStream::pair().unwrap();
            let kept = near.try_clone().unwrap();
            let budget = ::gandr_kernel_data::Budget::from(4096_usize);
            ::gandr_kernel_data::scoped::<(), _, _>(budget, |region, _mint| {
                let mut buf = harness::lend(region);
                crate::test::harness::runtime::new()
                    .run(async |scope| -> Result<(), crate::RuntimeError> {
                        let socket = harness::wrap(scope, near);
                        let recv = socket.recv(Buf::from(&mut *buf));
                        drop(recv);
                        Ok(())
                    })
                    .unwrap()
                    .unwrap();
                ::std::io::Write::write_all(&mut far, b"late").unwrap();
                let mut read = [0_u8; 4];
                ::std::io::Read::read_exact(&mut &kept, &mut read).unwrap();
                assert_eq!(&read, b"late");
                assert_eq!(&*buf, &[0_u8; 8]);
            });
        }
    }
}
