mod accept;
mod bind;
mod listen;
mod new;

use ::socket2::Domain;
use ::socket2::Protocol;
use ::socket2::SockAddr;
use ::socket2::Type;

use crate::io::socket::accept::OpSocketAccept;
use crate::io::socket::bind::OpSocketBind;
use crate::io::socket::listen::OpSocketListen;
use crate::io::socket::new::OpSocketNew;
use crate::scope::Scope;

#[non_exhaustive]
pub struct Socket<'tsk, 'env: 'tsk>
{
    scope: &'tsk Scope<'tsk, 'env>,
    inner: ::socket2::Socket,
}

impl<'tsk, 'env: 'tsk> Socket<'tsk, 'env>
{
    #[expect(clippy::new_ret_no_self, reason = "future")]
    #[must_use]
    pub fn new(
        scope: &'tsk Scope<'tsk, 'env>,
        domain: Domain,
        ty: Type,
        protocol: Option<Protocol>,
    ) -> OpSocketNew<'tsk, 'env>
    {
        OpSocketNew::new(scope, domain, ty, protocol)
    }

    #[must_use]
    pub fn bind(
        &self,
        addr: SockAddr,
    ) -> OpSocketBind<'tsk, 'env, '_>
    {
        let scope = self.scope;
        OpSocketBind::new(scope, &self.inner, addr)
    }

    #[must_use]
    pub fn listen(
        &self,
        backlog: ::core::ffi::c_int,
    ) -> OpSocketListen<'tsk, 'env, '_>
    {
        let scope = self.scope;
        OpSocketListen::new(scope, &self.inner, backlog)
    }

    #[must_use]
    pub fn accept(&self) -> OpSocketAccept<'tsk, 'env, '_>
    {
        let scope = self.scope;
        OpSocketAccept::new(scope, &self.inner)
    }
}

#[cfg(test)]
pub(crate) mod test
{
    #![expect(clippy::unwrap_used, reason = "cfg(test)")]

    use super::*;

    pub mod harness
    {
        use ::std::path::Path;

        use super::*;

        pub fn new<'tsk, 'env: 'tsk>(scope: &'tsk Scope<'tsk, 'env>) -> OpSocketNew<'tsk, 'env>
        {
            let domain = Domain::UNIX;
            let ty = Type::STREAM;
            let protocol = None;
            Socket::new(scope, domain, ty, protocol)
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
                .run(async |scope| -> ::anyhow::Result<()> {
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
            crate::test::harness::runtime::new()
                .run(async |scope| -> ::anyhow::Result<()> {
                    let temp = ::assert_fs::TempDir::new().unwrap();
                    let path = temp.child("socket");
                    let socket = crate::test::harness::io::socket::new(scope);
                    let socket = socket.await?;
                    path.assert(::predicates::path::exists().not());
                    let addr = ::socket2::SockAddr::unix(&path)?;
                    socket.bind(addr).await?;
                    path.assert(::predicates::path::exists());
                    Ok(())
                })
                .unwrap()
                .unwrap();
        }

        #[test]
        fn listen()
        {
            crate::test::harness::runtime::new()
                .run(async |scope| -> ::anyhow::Result<()> {
                    let temp = ::assert_fs::TempDir::new().unwrap();
                    let path = temp.child("socket");
                    let socket = crate::test::harness::io::socket::new(scope);
                    let socket = socket.await?;
                    path.assert(::predicates::path::exists().not());
                    let addr = ::socket2::SockAddr::unix(&path)?;
                    socket.bind(addr).await?;
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
            crate::test::harness::runtime::new()
                .run(async |scope| -> ::anyhow::Result<()> {
                    let socket = crate::test::harness::io::socket::new(scope);
                    let socket = socket.await?;
                    let addr = ::socket2::SockAddr::unix(&path)?;
                    socket.bind(addr).await?;
                    let backlog = ::libc::SOMAXCONN;
                    socket.listen(backlog).await?;
                    let (socket, sockaddr) = socket.accept().await?;
                    drop((socket, sockaddr));
                    Ok(())
                })
                .unwrap()
                .unwrap();
            connector.join().unwrap();
        }
    }
}
