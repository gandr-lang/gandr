mod accept;
mod bind;
mod listen;
mod new;
mod recv;

use ::socket2::Domain;
use ::socket2::Protocol;
use ::socket2::SockAddr;
use ::socket2::Type;

use crate::io::socket::accept::OpSocketAccept;
pub use crate::io::socket::accept::PeerAddr;
use crate::io::socket::bind::OpSocketBind;
use crate::io::socket::listen::OpSocketListen;
use crate::io::socket::new::OpSocketNew;
use crate::io::socket::recv::OpSocketRecv;
use crate::scope::Scope;

#[non_exhaustive]
pub struct Socket<'tsk, 'env>
{
    scope: &'tsk Scope<'tsk, 'env>,
    inner: ::socket2::Socket,
}

impl<'tsk, 'env: 'tsk> Socket<'tsk, 'env>
{
    #[expect(clippy::new_ret_no_self, reason = "future")]
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

    #[must_use]
    #[inline]
    pub fn listen(
        &self,
        backlog: ::core::ffi::c_int,
    ) -> OpSocketListen<'tsk, 'env, '_>
    {
        let scope = self.scope;
        OpSocketListen::new(scope, &self.inner, backlog)
    }

    /// An accept of a connection, whose peer's address the kernel writes
    /// into `peer`, storage lent for the scope's life.
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

    /// A receive of at most `buf.len()` bytes into `buf`, a buffer lent for
    /// the scope's life; the completion gives the count and the buffer back.
    #[must_use]
    #[inline]
    pub fn recv(
        &self,
        buf: &'tsk mut [u8],
    ) -> OpSocketRecv<'tsk, 'env, '_>
    {
        let scope = self.scope;
        OpSocketRecv::new(scope, &self.inner, buf)
    }
}

#[cfg(test)]
pub(crate) mod test
{
    use super::*;

    pub mod harness
    {
        use ::std::path::Path;

        use super::*;

        pub fn new<'tsk, 'env>(scope: &'tsk Scope<'tsk, 'env>) -> OpSocketNew<'tsk, 'env>
        {
            let domain = Domain::UNIX;
            let ty = Type::STREAM;
            let protocol = None;
            Socket::new(scope, domain, ty, protocol)
        }

        /// The near end of a connected pair as a socket of `scope`.
        pub fn wrap<'tsk, 'env>(
            scope: &'tsk Scope<'tsk, 'env>,
            near: ::std::os::unix::net::UnixStream,
        ) -> Socket<'tsk, 'env>
        {
            let inner = ::socket2::Socket::from(::std::os::fd::OwnedFd::from(near));
            Socket { scope, inner }
        }

        /// A buffer of `len` zero bytes, lent through the allocator of
        /// `region` for the region's life.
        pub fn lend<'region>(
            region: &'region ::gandr_kernel_data::Region<'_, (), ::alloc::alloc::Global>,
            len: usize,
        ) -> &'region mut [u8]
        {
            let mut bytes = ::alloc::vec::Vec::with_capacity_in(len, region);
            bytes.resize(len, 0_u8);
            bytes.leak()
        }
    }

    pub mod socket
    {
        use ::assert_fs::assert::PathAssert as _;
        use ::assert_fs::prelude::FileTouch as _;
        use ::assert_fs::prelude::PathChild as _;
        use ::predicates::prelude::PredicateBooleanExt as _;
        use ::std::path::Path;

        use super::*;

        #[test]
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
                    let backlog = ::libc::SOMAXCONN;
                    socket.listen(backlog).await?;
                    Ok(())
                })
                .unwrap()
                .unwrap();
        }

        #[test]
        fn accept()
        {
            let temp = ::assert_fs::TempDir::new().unwrap();
            let path = temp.child("socket");
            let connector = ::std::thread::spawn({
                let path = path.to_owned();
                move || loop {
                    if let Ok(stream) = ::std::os::unix::net::UnixStream::connect(&path) {
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
                    let backlog = ::libc::SOMAXCONN;
                    socket.listen(backlog).await?;
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
                    let backlog = ::libc::SOMAXCONN;
                    socket.listen(backlog).await?;
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
        fn recv()
        {
            let (near, mut far) = ::std::os::unix::net::UnixStream::pair().unwrap();
            ::std::io::Write::write_all(&mut far, b"ping").unwrap();
            let budget = ::gandr_kernel_data::Budget::from(4096_usize);
            ::gandr_kernel_data::scoped::<(), _, _>(budget, |region, _mint| {
                let buf = harness::lend(region, 8);
                let got = crate::test::harness::runtime::new()
                    .run(
                        async |scope| -> Result<Option<Vec<u8>>, crate::RuntimeError> {
                            let socket = harness::wrap(scope, near);
                            let (len, buf) = socket.recv(buf).await?;
                            Ok(buf.get(.. len).map(<[u8]>::to_vec))
                        },
                    )
                    .unwrap()
                    .unwrap();
                assert_eq!(got.as_deref(), Some(b"ping".as_slice()));
            });
        }

        /// A scope that ends with a receive in flight cancels it before the
        /// run returns. So the bytes that the peer sends after the run stay
        /// in the socket, and the region's buffer keeps its zeros.
        #[test]
        fn recv_in_flight()
        {
            let (near, mut far) = ::std::os::unix::net::UnixStream::pair().unwrap();
            let kept = near.try_clone().unwrap();
            let budget = ::gandr_kernel_data::Budget::from(4096_usize);
            ::gandr_kernel_data::scoped::<(), _, _>(budget, |region, _mint| {
                let buf = harness::lend(region, 8);
                crate::test::harness::runtime::new()
                    .run(async |scope| -> Result<(), crate::RuntimeError> {
                        let socket = harness::wrap(scope, near);
                        let recv = socket.recv(&mut *buf);
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
