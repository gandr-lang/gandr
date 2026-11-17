//! The preparers of binds of sockets to addresses.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use ::std::os::fd::AsRawFd as _;

    use crate::fd::SlotDesc;
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for a bind of `socket` to `addr`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `addr` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion.
        ///   `socket` is an open descriptor, or a slot of the ring's file table
        ///   when the entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_bind<'op>(
            &mut self,
            socket: SlotDesc<&'op ::socket2::Socket>,
            addr: &'op ::socket2::SockAddr,
        )
        {
            let sqe = &raw mut *self.sqe();

            let fd = socket.as_raw_fd();
            // liburing's signature takes a mutable address here, though the
            // kernel only reads it; the cast leaves when liburing
            // takes a constant address.
            let addrlen = addr.len();
            let addr = ::core::ptr::from_ref(addr).cast_mut();
            let addr = addr.cast();

            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_bind(sqe, fd, addr, addrlen);
            }
        }
    }
}

#[cfg(test)]
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        single_field_struct_needs_transparent_repr,
        reason = "the builder's macro makes a struct for each field of the fixture, and the source has no struct to mark; #7729 owes the lint's reading of a macro's structs"
    )
)]
pub mod test
{
    use ::assert_fs::TempDir;
    use ::assert_fs::assert::PathAssert as _;
    use ::assert_fs::fixture::ChildPath;
    use ::assert_fs::prelude::PathChild as _;
    use ::notify::Watcher as _;

    use crate::IoUring;
    use crate::arg::Answer;
    use crate::arg::Count;
    use crate::arg::Flags;
    use crate::arg::Index;
    use crate::arg::Switch;
    use crate::fd::SlotDesc;
    use crate::sys::SysResult as _;

    #[derive(::bon::Builder)]
    pub struct Fixture<'op>
    {
        #[builder(start_fn)]
        socket: SlotDesc<&'op ::socket2::Socket>,
        #[builder(start_fn)]
        addr: ::socket2::SockAddr,
        #[builder(default = Switch(false))]
        sqe_link: Switch,
        #[builder(default = Switch(false))]
        cqe_skip: Switch,
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
                ref addr,
                sqe_link,
                cqe_skip,
            } = self;

            let mut sq = ring.squeue();
            let mut sqe = sq
                .get_sqe()
                .ok_or_else(|| ::std::io::Error::other("failed to get sqe"))
                .unwrap();
            // SAFETY: `addr` lives until the fixture reads the completion, and
            // `socket` stays open for the test.
            unsafe {
                sqe.prep_bind(socket, addr);
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
        ) where
            C: crate::cqe::Kind,
            S: crate::sqe::Kind,
        {
            let num = self.submit(ring);
            assert_eq!(Count(1), num);

            let mut cq = ring.cqueue();

            let cqe = cq
                .wait(Count(1))
                .unwrap()
                .next()
                .map(Into::into)
                .ok_or_else(|| ::std::io::Error::other("failed to get cqe"))
                .unwrap();
            Answer(cqe.cqe().res).sys_zero().unwrap();
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

    /// Runs the bind fixture on `ring` with these arguments.
    ///
    /// # Specification
    ///
    /// trivial.
    pub fn bind_with<S, C>(
        ring: &mut IoUring<'_, S, C>,
        temp: &::assert_fs::TempDir,
        path: &ChildPath,
        socket: &SlotDesc<::socket2::Socket>,
        sqe_link: Option<Switch>,
        cqe_skip: Option<Switch>,
    ) where
        C: crate::cqe::Kind,
        S: crate::sqe::Kind,
    {
        let (bind_tx, bind_rx) = ::std::sync::mpsc::channel();
        let mut watcher = ::notify::recommended_watcher(bind_tx).unwrap();
        watcher
            .watch(temp, ::notify::RecursiveMode::Recursive)
            .unwrap();

        let socket = socket.as_ref();
        let addr = ::socket2::SockAddr::unix(path).unwrap();
        crate::sqe::bind::test::Fixture::builder(socket, addr)
            .maybe_sqe_link(sqe_link)
            .maybe_cqe_skip(cqe_skip)
            .build()
            .run(ring);

        let event = bind_rx
            .recv_timeout(::core::time::Duration::from_secs(1))
            .unwrap()
            .unwrap();
        assert!(event.paths.iter().any(|p| p.as_path() == path.as_ref()));

        path.assert(::predicates::path::exists());
    }

    #[test]
    #[cfg_attr(
        miri,
        ignore = "it sets up a ring through liburing, which Miri cannot run"
    )]
    fn bind()
    {
        let temp = TempDir::new().map_err(::std::io::Error::other).unwrap();
        let path = temp.child("socket");

        let slots = None;
        let socket_slot = None;

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

        let sqe_link = None;
        let cqe_skip = None;

        crate::sqe::bind::test::bind_with(&mut ring, &temp, &path, &socket, sqe_link, cqe_skip);
    }

    #[test]
    #[cfg_attr(
        miri,
        ignore = "it sets up a ring through liburing, which Miri cannot run"
    )]
    fn bind_direct()
    {
        let temp = TempDir::new().map_err(::std::io::Error::other).unwrap();
        let path = temp.child("socket");

        let slots = Some(Count(1));
        let socket_slot = Some(Index(
            ::liburing_rs::IORING_FILE_INDEX_ALLOC.cast_unsigned(),
        ));

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

        let sqe_link = None;
        let cqe_skip = None;

        crate::sqe::bind::test::bind_with(&mut ring, &temp, &path, &socket, sqe_link, cqe_skip);
    }

    #[test]
    #[cfg_attr(
        miri,
        ignore = "it sets up a ring through liburing, which Miri cannot run"
    )]
    fn bind_direct_cqe_skip()
    {
        let temp = TempDir::new().map_err(::std::io::Error::other).unwrap();
        let path = temp.child("socket");

        let slots = Some(Count(1));
        let socket_slot = Some(Index(0));

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

        let sqe_link = None;
        let cqe_skip = Some(Switch(true));

        crate::sqe::bind::test::bind_with(&mut ring, &temp, &path, &socket, sqe_link, cqe_skip);
    }
}
