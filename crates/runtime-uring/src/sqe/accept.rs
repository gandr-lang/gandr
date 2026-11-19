//! The preparers of accepts of connections.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use ::std::os::fd::AsRawFd as _;

    use crate::arg::Index;
    use crate::arg::Len;
    use crate::arg::Switch;
    use crate::fd::SlotDesc;
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for an accept of one connection on `socket`, with
        /// the peer's address written to `addr` and `addrlen`.
        /// With `file_index` the kernel puts the new socket in that slot of the
        /// ring's file table.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `addr` and `addrlen` point to memory that stays
        ///   valid, and does not move, until the kernel posts the entry's
        ///   completion. `socket` is an open descriptor, or a slot of the
        ///   ring's file table when the entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_accept<'op>(
            &mut self,
            socket: SlotDesc<&'op ::socket2::Socket>,
            addr: &'op mut ::socket2::SockAddrStorage,
            Len(addrlen): Len<&'op mut ::socket2::socklen_t>,
            flags: ::rustix::net::SocketFlags,
            file_index: Option<Index<::core::ffi::c_uint>>,
        )
        {
            let sqe = &raw mut *self.sqe();

            let fd = socket.as_raw_fd();
            // SAFETY: `addr` is the storage of a socket address, which the
            // kernel fills; `view_as` gives the same bytes as a
            // `sockaddr`.
            let addr = unsafe { addr.view_as() };
            let flags = flags.bits().cast_signed();

            if let Some(Index(file_index)) = file_index {
                // SAFETY: The enclosing method preserves the safety interface.
                unsafe {
                    ::liburing_rs::io_uring_prep_accept_direct(
                        sqe,
                        fd,
                        &raw mut *addr,
                        &raw mut *addrlen,
                        flags,
                        file_index,
                    );
                }
            }
            else {
                // SAFETY: The enclosing method preserves the safety interface.
                unsafe {
                    ::liburing_rs::io_uring_prep_accept(
                        sqe,
                        fd,
                        &raw mut *addr,
                        &raw mut *addrlen,
                        flags,
                    );
                }
            }
        }

        /// Prepares the entry for an accept that stays armed and posts one
        /// completion for each connection on `socket`.
        /// With `direct` the kernel puts each new socket in a free slot of the
        /// ring's file table.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `addr` and `addrlen` point to memory that stays
        ///   valid, and does not move, until the kernel posts the entry's
        ///   completion. `socket` is an open descriptor, or a slot of the
        ///   ring's file table when the entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_multishot_accept<'op>(
            &mut self,
            socket: SlotDesc<&'op ::socket2::Socket>,
            addr: &'op mut ::socket2::SockAddrStorage,
            Len(addrlen): Len<&'op mut ::socket2::socklen_t>,
            flags: ::rustix::net::SocketFlags,
            Switch(direct): Switch,
        )
        {
            let sqe = &raw mut *self.sqe();

            let fd = socket.as_raw_fd();
            // SAFETY: `addr` is the storage of a socket address, which the
            // kernel fills; `view_as` gives the same bytes as a
            // `sockaddr`.
            let addr = unsafe { addr.view_as() };
            let flags = flags.bits().cast_signed();

            if direct {
                // SAFETY: The enclosing method preserves the safety interface.
                unsafe {
                    ::liburing_rs::io_uring_prep_multishot_accept_direct(
                        sqe,
                        fd,
                        &raw mut *addr,
                        &raw mut *addrlen,
                        flags,
                    );
                }
            }
            else {
                // SAFETY: The enclosing method preserves the safety interface.
                unsafe {
                    ::liburing_rs::io_uring_prep_multishot_accept(
                        sqe,
                        fd,
                        &raw mut *addr,
                        &raw mut *addrlen,
                        flags,
                    );
                }
            }
        }
    }
}

#[cfg(test)]
pub mod test
{
    use ::assert_fs::TempDir;
    // use ::assert_fs::assert::PathAssert as _;
    use ::assert_fs::prelude::PathChild as _;
    // use ::notify::Watcher as _;
    use ::std::os::fd::FromRawFd as _;
    use ::std::path::Path;

    use crate::Cqe16;
    use crate::IoUring;
    use crate::arg::Answer;
    use crate::arg::Count;
    use crate::arg::Flags;
    use crate::arg::Holds;
    use crate::arg::Index;
    use crate::arg::Len;
    use crate::arg::Switch;
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
        client_slot: Option<Index<::core::ffi::c_uint>>,
        #[builder(default = Switch(false))]
        sqe_link: Switch,
        #[builder(default = Switch(false))]
        cqe_skip: Switch,
    }

    impl<'fds, S: self::fixture_builder::IsComplete> FixtureBuilder<'fds, S>
    {
        /// The fixture that the builder holds.
        ///
        /// # Specification
        ///
        /// trivial.
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
        /// Prepares the fixture's entry and submits it, and gives the count of
        /// entries that the kernel takes.
        ///
        /// # Specification
        ///
        /// trivial.
        fn submit<S, C>(
            self,
            ring: &mut IoUring<'_, S, C>,
        ) -> Count<u32>
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
                // SAFETY: the fixture owns `addr` and `addrlen` until it reads the
                // completion, and `socket` stays open for the test.
                FixtureOpMode::Singleshot => unsafe {
                    sqe.prep_accept(socket, addr, Len(addrlen), flags, client_slot);
                },
                // SAFETY: the fixture owns `addr` and `addrlen` until it reads the last
                // completion, and `socket` stays open for the test.
                FixtureOpMode::Multishot { direct, .. } => unsafe {
                    sqe.prep_multishot_accept(socket, addr, Len(addrlen), flags, Switch(direct));
                },
            }

            let mut flags = ::core::ffi::c_uint::default();
            if sqe_link.0 {
                flags |= ::liburing_rs::IOSQE_IO_LINK;
            }
            if cqe_skip.0 {
                flags |= ::liburing_rs::IOSQE_CQE_SKIP_SUCCESS;
            }
            if socket.is_slot().0 {
                flags |= ::liburing_rs::IOSQE_FIXED_FILE;
            }
            // SAFETY: each flag is the kernel's, and the fixed-file flag goes
            // with a slot alone.
            unsafe {
                sqe.set_flags(Flags(flags));
            }

            sq.submit().unwrap()
        }

        /// Submits the fixture's entry and waits for its completion.
        ///
        /// # Specification
        ///
        /// trivial.
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
            let Holds(uses_slot) = self.socket.is_slot();

            let num = self.submit(ring);
            assert_eq!(Count(1), num);

            let mut descs = vec![];

            let mut cq = ring.cqueue();

            for i in 0 .. clients {
                let cqe = cq
                    .wait(Count(1))
                    .unwrap()
                    .next()
                    .map(Into::<Cqe16<'_>>::into)
                    .ok_or_else(|| ::std::io::Error::other("failed to get cqe"))
                    .unwrap();

                let Answer(desc) = Answer(cqe.cqe().res).sys_uint().unwrap();
                let desc = if uses_slot {
                    SlotDesc::Slot(desc)
                }
                else {
                    let fd = desc.cast_signed();
                    // SAFETY: the completion gives a new descriptor, which this
                    // socket owns alone from here.
                    unsafe { ::socket2::Socket::from_raw_fd(fd) }.into()
                };

                descs.push(desc);

                if i.checked_add(1).is_some_and(|next| next < clients) {
                    assert_ne!(0, cqe.cqe().flags & ::liburing_rs::IORING_CQE_F_MORE);
                }
            }
            assert_eq!(descs.len(), clients);

            descs
        }

        /// Runs the fixture on `ring` and checks the outcome.
        ///
        /// # Specification
        ///
        /// trivial.
        pub fn run<S, C>(
            self,
            ring: &mut IoUring<'_, S, C>,
        ) where
            C: crate::cqe::Kind,
            S: crate::sqe::Kind,
        {
            if self.cqe_skip.0 {
                self.submit(ring);
            }
            else {
                self.submit_and_wait(ring);
            }
        }
    }

    /// Connects a client to the socket at `path` on a thread of its own.
    ///
    /// # Specification
    ///
    /// trivial.
    pub fn connect(path: &Path) -> ::std::thread::JoinHandle<::std::io::Result<()>>
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

    /// Runs the accept fixture `fixture`, the accept's fields in one struct,
    /// on `ring`.
    ///
    /// # Specification
    ///
    /// trivial.
    pub fn accept_with<S, C>(
        ring: &mut IoUring<'_, S, C>,
        fixture: Fixture<'_>,
    ) where
        C: crate::cqe::Kind,
        S: crate::sqe::Kind,
    {
        fixture.run(ring);
    }

    #[test]
    #[cfg_attr(
        miri,
        ignore = "it sets up a ring through liburing, which Miri cannot run"
    )]
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

        let sqe_link = Some(Switch(true));
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

        let fixture = crate::sqe::accept::test::Fixture::builder(
            socket.as_ref(),
            &mut addr,
            &mut addrlen,
            mode,
        )
        .maybe_client_slot(client_slot)
        .maybe_sqe_link(sqe_link)
        .maybe_cqe_skip(cqe_skip)
        .build();
        crate::sqe::accept::test::accept_with(&mut ring, fixture);

        for thread in threads {
            thread.join().unwrap().unwrap();
        }
    }

    #[test]
    #[cfg_attr(
        miri,
        ignore = "it sets up a ring through liburing, which Miri cannot run"
    )]
    fn accept_direct()
    {
        let temp = TempDir::new().map_err(::std::io::Error::other).unwrap();
        let path = temp.child("socket");

        let mut addr = ::socket2::SockAddrStorage::zeroed();
        let mut addrlen = ::socket2::socklen_t::default();

        let clients = 1;
        let client_slot = Some(Index(
            ::liburing_rs::IORING_FILE_INDEX_ALLOC.cast_unsigned(),
        ));

        let slots = Some(Count(1 + u32::try_from(clients).unwrap()));
        let socket_slot = Some(Index(
            ::liburing_rs::IORING_FILE_INDEX_ALLOC.cast_unsigned(),
        ));
        let mode = FixtureOpMode::Singleshot;

        let mut ring = IoUring::new().unwrap();

        let sqe_link = Some(Switch(true));
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

        let fixture = crate::sqe::accept::test::Fixture::builder(
            socket.as_ref(),
            &mut addr,
            &mut addrlen,
            mode,
        )
        .maybe_client_slot(client_slot)
        .maybe_sqe_link(sqe_link)
        .maybe_cqe_skip(cqe_skip)
        .build();
        crate::sqe::accept::test::accept_with(&mut ring, fixture);

        for thread in threads {
            thread.join().unwrap().unwrap();
        }
    }

    #[test]
    #[cfg_attr(
        miri,
        ignore = "it sets up a ring through liburing, which Miri cannot run"
    )]
    fn accept_direct_cqe_skip()
    {
        let temp = TempDir::new().map_err(::std::io::Error::other).unwrap();
        let path = temp.child("socket");

        let mut addr = ::socket2::SockAddrStorage::zeroed();
        let mut addrlen = ::socket2::socklen_t::default();

        let clients = 1;
        let client_slot = Some(Index(1));

        let slots = Some(Count(1 + u32::try_from(clients).unwrap()));
        let socket_slot = Some(Index(0));
        let mode = FixtureOpMode::Singleshot;

        let mut ring = IoUring::new().unwrap();

        let sqe_link = Some(Switch(true));
        let cqe_skip = Some(Switch(true));

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

        // The listen posts no completion, so the test waits for it through
        // the clients: a connect to a Unix socket succeeds only once the
        // socket listens, and the kernel keeps each connection in the backlog
        // for the accept. Without this wait the accept can reach the socket
        // before its listen and fail with `EINVAL`.
        for thread in threads {
            thread.join().unwrap().unwrap();
        }

        let fixture = crate::sqe::accept::test::Fixture::builder(
            socket.as_ref(),
            &mut addr,
            &mut addrlen,
            mode,
        )
        .maybe_client_slot(client_slot)
        .maybe_sqe_link(sqe_link)
        .maybe_cqe_skip(cqe_skip)
        .build();
        crate::sqe::accept::test::accept_with(&mut ring, fixture);
    }

    #[test]
    #[cfg_attr(
        miri,
        ignore = "it sets up a ring through liburing, which Miri cannot run"
    )]
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

        let sqe_link = Some(Switch(true));
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

        let fixture = crate::sqe::accept::test::Fixture::builder(
            socket.as_ref(),
            &mut addr,
            &mut addrlen,
            mode,
        )
        .maybe_client_slot(client_slot)
        .maybe_sqe_link(sqe_link)
        .maybe_cqe_skip(cqe_skip)
        .build();
        crate::sqe::accept::test::accept_with(&mut ring, fixture);

        for thread in threads {
            thread.join().unwrap().unwrap();
        }
    }

    #[test]
    #[cfg_attr(
        miri,
        ignore = "it sets up a ring through liburing, which Miri cannot run"
    )]
    fn accept_multishot_direct()
    {
        let temp = TempDir::new().map_err(::std::io::Error::other).unwrap();
        let path = temp.child("socket");

        let mut addr = ::socket2::SockAddrStorage::zeroed();
        let mut addrlen = ::socket2::socklen_t::default();

        let clients = 4;
        let client_slot = None;

        let slots = Some(Count(1 + u32::try_from(clients).unwrap()));
        let socket_slot = Some(Index(
            ::liburing_rs::IORING_FILE_INDEX_ALLOC.cast_unsigned(),
        ));
        let mode = FixtureOpMode::Multishot {
            clients,
            direct: true,
        };

        let mut ring = IoUring::new().unwrap();

        let sqe_link = Some(Switch(true));
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

        let fixture = crate::sqe::accept::test::Fixture::builder(
            socket.as_ref(),
            &mut addr,
            &mut addrlen,
            mode,
        )
        .maybe_client_slot(client_slot)
        .maybe_sqe_link(sqe_link)
        .maybe_cqe_skip(cqe_skip)
        .build();
        crate::sqe::accept::test::accept_with(&mut ring, fixture);

        for thread in threads {
            thread.join().unwrap().unwrap();
        }
    }
}
