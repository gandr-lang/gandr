pub mod repr
{
    use ::std::os::fd::AsRawFd as _;

    use crate::fd::SlotDesc;
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        pub unsafe fn prep_accept<'op>(
            &mut self,
            socket: SlotDesc<&'op ::socket2::Socket>,
            addr: &'op mut ::socket2::SockAddrStorage,
            addrlen: &'op mut ::socket2::socklen_t,
            flags: ::rustix::net::SocketFlags,
            file_index: Option<::core::ffi::c_uint>,
        )
        {
            let sqe = &raw mut *self.sqe;

            let fd = socket.as_raw_fd();
            // SAFETY:
            let addr = unsafe { addr.view_as() };
            let flags = flags.bits().cast_signed();

            if let Some(file_index) = file_index {
                // SAFETY: The enclosing method preserves the safety interface.
                unsafe {
                    ::liburing_rs::io_uring_prep_accept_direct(
                        sqe, fd, addr, addrlen, flags, file_index,
                    )
                };
            }
            else {
                // SAFETY: The enclosing method preserves the safety interface.
                unsafe { ::liburing_rs::io_uring_prep_accept(sqe, fd, addr, addrlen, flags) };
            }
        }

        pub unsafe fn prep_multishot_accept<'op>(
            &mut self,
            socket: SlotDesc<&'op ::socket2::Socket>,
            addr: &'op mut ::socket2::SockAddrStorage,
            addrlen: &'op mut ::socket2::socklen_t,
            flags: ::rustix::net::SocketFlags,
            direct: bool,
        )
        {
            let sqe = &raw mut *self.sqe;

            let fd = socket.as_raw_fd();
            // SAFETY:
            let addr = unsafe { addr.view_as() };
            let flags = flags.bits().cast_signed();

            if direct {
                // SAFETY: The enclosing method preserves the safety interface.
                unsafe {
                    ::liburing_rs::io_uring_prep_multishot_accept_direct(
                        sqe, fd, addr, addrlen, flags,
                    )
                };
            }
            else {
                // SAFETY: The enclosing method preserves the safety interface.
                unsafe {
                    ::liburing_rs::io_uring_prep_multishot_accept(sqe, fd, addr, addrlen, flags)
                };
            }
        }
    }
}

#[cfg(test)]
pub(crate) mod test
{
    use ::assert_fs::TempDir;
    // use ::assert_fs::assert::PathAssert as _;
    use ::assert_fs::prelude::PathChild as _;
    // use ::notify::Watcher as _;
    use ::std::os::fd::FromRawFd as _;
    use ::std::path::Path;

    use crate::Cqe16;
    use crate::IoUring;
    use crate::fd::SlotDesc;
    use crate::sys::SysResult as _;

    pub enum FixtureOpMode
    {
        Singleshot,
        Multishot
        {
            clients: usize,
            direct: bool,
        },
    }

    #[derive(::bon::Builder)]
    #[builder(finish_fn(vis = "", name = build_internal))]
    pub struct Fixture<'op>
    {
        #[builder(start_fn)]
        socket: SlotDesc<&'op ::socket2::Socket>,
        #[builder(start_fn)]
        addr: &'op mut ::socket2::SockAddrStorage,
        #[builder(start_fn)]
        addrlen: &'op mut ::socket2::socklen_t,
        #[builder(start_fn)]
        mode: FixtureOpMode,
        #[builder(default = ::rustix::net::SocketFlags::empty())]
        flags: ::rustix::net::SocketFlags,
        client_slot: Option<::core::ffi::c_uint>,
        #[builder(default = false)]
        sqe_link: bool,
        #[builder(default = false)]
        cqe_skip: bool,
    }

    impl<'fds, S: self::fixture_builder::IsComplete> FixtureBuilder<'fds, S>
    {
        pub fn build(self) -> Fixture<'fds>
        {
            let this = self.build_internal();

            if matches!(this.mode, FixtureOpMode::Multishot { direct: true, .. }) {
                assert!(
                    this.client_slot.is_none(),
                    "client_slot is not supported with multishot direct mode"
                );
            }

            this
        }
    }

    impl Fixture<'_>
    {
        fn submit<S, C>(
            self,
            ring: &mut IoUring<'_, S, C>,
        ) -> u32
        where
            C: crate::cqe::Kind,
            S: crate::sqe::Kind,
        {
            let Self {
                socket,
                addr,
                addrlen,
                mode,
                flags,
                client_slot,
                sqe_link,
                cqe_skip,
            } = self;

            let mut sq = ring.squeue();
            let mut sqe = sq
                .get_sqe()
                .ok_or_else(|| ::std::io::Error::other("failed to get sqe"))
                .unwrap();

            match mode {
                FixtureOpMode::Singleshot => {
                    unsafe { sqe.prep_accept(socket, addr, addrlen, flags, client_slot) };
                },
                FixtureOpMode::Multishot { direct, .. } => {
                    unsafe { sqe.prep_multishot_accept(socket, addr, addrlen, flags, direct) };
                },
            }

            let mut flags = ::core::ffi::c_uint::default();
            if sqe_link {
                flags |= ::liburing_rs::IOSQE_IO_LINK;
            }
            if cqe_skip {
                flags |= ::liburing_rs::IOSQE_CQE_SKIP_SUCCESS;
            }
            if socket.is_slot() {
                flags |= ::liburing_rs::IOSQE_FIXED_FILE;
            }
            unsafe { sqe.set_flags(flags) };

            sq.submit().unwrap()
        }

        fn submit_and_wait<S, C>(
            self,
            ring: &mut IoUring<'_, S, C>,
        ) -> Vec<SlotDesc<::socket2::Socket>>
        where
            C: crate::cqe::Kind,
            S: crate::sqe::Kind,
        {
            let clients = if let FixtureOpMode::Multishot { clients, .. } = self.mode {
                clients
            }
            else {
                1
            };
            let uses_slot = self.socket.is_slot();

            let num = self.submit(ring);
            assert_eq!(1, num);

            let mut descs = vec![];

            let mut cq = ring.cqueue();

            for i in 0 .. clients {
                let cqe = cq
                    .wait(1)
                    .unwrap()
                    .next()
                    .map(Into::<Cqe16<'_>>::into)
                    .ok_or_else(|| ::std::io::Error::other("failed to get cqe"))
                    .unwrap();

                let desc = cqe.cqe.res.sys_uint().unwrap();
                let desc = if uses_slot {
                    SlotDesc::Slot(desc)
                }
                else {
                    let fd = desc.cast_signed();
                    unsafe { ::socket2::Socket::from_raw_fd(fd) }.into()
                };

                descs.push(desc);

                if i + 1 < clients {
                    assert_ne!(0, cqe.cqe.flags & ::liburing_rs::IORING_CQE_F_MORE);
                }
            }
            assert_eq!(descs.len(), clients);

            descs
        }

        pub fn run<S, C>(
            self,
            ring: &mut IoUring<'_, S, C>,
        ) where
            C: crate::cqe::Kind,
            S: crate::sqe::Kind,
        {
            if self.cqe_skip {
                self.submit(ring);
            }
            else {
                self.submit_and_wait(ring);
            }
        }
    }

    pub(crate) fn connect(path: &Path) -> ::std::thread::JoinHandle<::std::io::Result<()>>
    {
        ::std::thread::spawn({
            let path = path.to_path_buf();
            move || -> ::std::io::Result<()> {
                loop {
                    if ::std::os::unix::net::UnixStream::connect(&path).is_ok() {
                        break;
                    }
                    ::core::hint::spin_loop();
                }
                Ok(())
            }
        })
    }

    pub(crate) fn accept_with<'op, S, C>(
        ring: &mut IoUring<'_, S, C>,
        socket: &SlotDesc<::socket2::Socket>,
        addr: &'op mut ::socket2::SockAddrStorage,
        addrlen: &'op mut ::socket2::socklen_t,
        client_slot: Option<::core::ffi::c_uint>,
        mode: FixtureOpMode,
        sqe_link: Option<bool>,
        cqe_skip: Option<bool>,
    ) where
        C: crate::cqe::Kind,
        S: crate::sqe::Kind,
    {
        let socket = socket.as_ref();
        crate::sqe::accept::test::Fixture::builder(socket, addr, addrlen, mode)
            .maybe_client_slot(client_slot)
            .maybe_sqe_link(sqe_link)
            .maybe_cqe_skip(cqe_skip)
            .build()
            .run(ring);
    }

    #[test]
    fn accept()
    {
        let temp = TempDir::new().map_err(::std::io::Error::other).unwrap();
        let path = temp.child("socket");

        let mut addr = ::socket2::SockAddrStorage::zeroed();
        let mut addrlen = ::socket2::socklen_t::default();

        let clients = 1;
        let client_slot = None;

        let slots = None;
        let socket_slot = None;
        let mode = FixtureOpMode::Singleshot;

        let mut ring = IoUring::new().unwrap();

        let sqe_link = Some(true);
        let cqe_skip = None;

        let socket = crate::sqe::socket::test::socket_with(
            &mut ring,
            slots,
            socket_slot,
            sqe_link,
            cqe_skip,
        );
        crate::sqe::bind::test::bind_with(&mut ring, &temp, &path, &socket, sqe_link, cqe_skip);
        crate::sqe::listen::test::listen_with(&mut ring, &socket, sqe_link, cqe_skip);

        let sqe_link = None;
        let cqe_skip = None;

        let threads = ::core::iter::repeat_with(|| crate::sqe::accept::test::connect(&path))
            .take(clients)
            .collect::<Vec<_>>();

        crate::sqe::accept::test::accept_with(
            &mut ring,
            &socket,
            &mut addr,
            &mut addrlen,
            client_slot,
            mode,
            sqe_link,
            cqe_skip,
        );

        for thread in threads {
            thread.join().unwrap().unwrap();
        }
    }

    #[test]
    fn accept_direct()
    {
        let temp = TempDir::new().map_err(::std::io::Error::other).unwrap();
        let path = temp.child("socket");

        let mut addr = ::socket2::SockAddrStorage::zeroed();
        let mut addrlen = ::socket2::socklen_t::default();

        let clients = 1;
        let client_slot = Some(::liburing_rs::IORING_FILE_INDEX_ALLOC.cast_unsigned());

        let slots = Some(1 + u32::try_from(clients).unwrap());
        let socket_slot = Some(::liburing_rs::IORING_FILE_INDEX_ALLOC.cast_unsigned());
        let mode = FixtureOpMode::Singleshot;

        let mut ring = IoUring::new().unwrap();

        let sqe_link = Some(true);
        let cqe_skip = None;

        let socket = crate::sqe::socket::test::socket_with(
            &mut ring,
            slots,
            socket_slot,
            sqe_link,
            cqe_skip,
        );
        crate::sqe::bind::test::bind_with(&mut ring, &temp, &path, &socket, sqe_link, cqe_skip);
        crate::sqe::listen::test::listen_with(&mut ring, &socket, sqe_link, cqe_skip);

        let sqe_link = None;
        let cqe_skip = None;

        let threads = ::core::iter::repeat_with(|| crate::sqe::accept::test::connect(&path))
            .take(clients)
            .collect::<Vec<_>>();

        crate::sqe::accept::test::accept_with(
            &mut ring,
            &socket,
            &mut addr,
            &mut addrlen,
            client_slot,
            mode,
            sqe_link,
            cqe_skip,
        );

        for thread in threads {
            thread.join().unwrap().unwrap();
        }
    }

    #[test]
    fn accept_direct_cqe_skip()
    {
        let temp = TempDir::new().map_err(::std::io::Error::other).unwrap();
        let path = temp.child("socket");

        let mut addr = ::socket2::SockAddrStorage::zeroed();
        let mut addrlen = ::socket2::socklen_t::default();

        let clients = 1;
        let client_slot = Some(1);

        let slots = Some(1 + u32::try_from(clients).unwrap());
        let socket_slot = Some(0);
        let mode = FixtureOpMode::Singleshot;

        let mut ring = IoUring::new().unwrap();

        let sqe_link = Some(true);
        let cqe_skip = Some(true);

        let socket = crate::sqe::socket::test::socket_with(
            &mut ring,
            slots,
            socket_slot,
            sqe_link,
            cqe_skip,
        );
        crate::sqe::bind::test::bind_with(&mut ring, &temp, &path, &socket, sqe_link, cqe_skip);
        crate::sqe::listen::test::listen_with(&mut ring, &socket, sqe_link, cqe_skip);

        let sqe_link = None;
        let cqe_skip = None;

        let threads = ::core::iter::repeat_with(|| crate::sqe::accept::test::connect(&path))
            .take(clients)
            .collect::<Vec<_>>();

        crate::sqe::accept::test::accept_with(
            &mut ring,
            &socket,
            &mut addr,
            &mut addrlen,
            client_slot,
            mode,
            sqe_link,
            cqe_skip,
        );

        for thread in threads {
            thread.join().unwrap().unwrap();
        }
    }

    #[test]
    fn accept_multishot()
    {
        let temp = TempDir::new().map_err(::std::io::Error::other).unwrap();
        let path = temp.child("socket");

        let mut addr = ::socket2::SockAddrStorage::zeroed();
        let mut addrlen = ::socket2::socklen_t::default();

        let clients = 4;
        let client_slot = None;

        let slots = None;
        let socket_slot = None;
        let mode = FixtureOpMode::Multishot {
            clients,
            direct: false,
        };

        let mut ring = IoUring::new().unwrap();

        let sqe_link = Some(true);
        let cqe_skip = None;

        let socket = crate::sqe::socket::test::socket_with(
            &mut ring,
            slots,
            socket_slot,
            sqe_link,
            cqe_skip,
        );
        crate::sqe::bind::test::bind_with(&mut ring, &temp, &path, &socket, sqe_link, cqe_skip);
        crate::sqe::listen::test::listen_with(&mut ring, &socket, sqe_link, cqe_skip);

        let sqe_link = None;
        let cqe_skip = None;

        let threads = ::core::iter::repeat_with(|| crate::sqe::accept::test::connect(&path))
            .take(clients)
            .collect::<Vec<_>>();

        crate::sqe::accept::test::accept_with(
            &mut ring,
            &socket,
            &mut addr,
            &mut addrlen,
            client_slot,
            mode,
            sqe_link,
            cqe_skip,
        );

        for thread in threads {
            thread.join().unwrap().unwrap();
        }
    }

    #[test]
    fn accept_multishot_direct()
    {
        let temp = TempDir::new().map_err(::std::io::Error::other).unwrap();
        let path = temp.child("socket");

        let mut addr = ::socket2::SockAddrStorage::zeroed();
        let mut addrlen = ::socket2::socklen_t::default();

        let clients = 4;
        let client_slot = None;

        let slots = Some(1 + u32::try_from(clients).unwrap());
        let socket_slot = Some(::liburing_rs::IORING_FILE_INDEX_ALLOC.cast_unsigned());
        let mode = FixtureOpMode::Multishot {
            clients,
            direct: true,
        };

        let mut ring = IoUring::new().unwrap();

        let sqe_link = Some(true);
        let cqe_skip = None;

        let socket = crate::sqe::socket::test::socket_with(
            &mut ring,
            slots,
            socket_slot,
            sqe_link,
            cqe_skip,
        );
        crate::sqe::bind::test::bind_with(&mut ring, &temp, &path, &socket, sqe_link, cqe_skip);
        crate::sqe::listen::test::listen_with(&mut ring, &socket, sqe_link, cqe_skip);

        let sqe_link = None;
        let cqe_skip = None;

        let threads = ::core::iter::repeat_with(|| crate::sqe::accept::test::connect(&path))
            .take(clients)
            .collect::<Vec<_>>();

        crate::sqe::accept::test::accept_with(
            &mut ring,
            &socket,
            &mut addr,
            &mut addrlen,
            client_slot,
            mode,
            sqe_link,
            cqe_skip,
        );

        for thread in threads {
            thread.join().unwrap().unwrap();
        }
    }
}
