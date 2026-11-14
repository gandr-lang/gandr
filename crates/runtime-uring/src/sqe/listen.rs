pub mod repr
{
    use ::std::os::fd::AsRawFd as _;

    use crate::fd::SlotDesc;
    use crate::sqe::repr::Sqe64;

    impl<'op> Sqe64<'op>
    {
        // #[expect(clippy::needless_pass_by_value, reason = "avoid
        // indirection")]
        #[inline]
        pub unsafe fn prep_listen(
            &mut self,
            socket: SlotDesc<&'op ::socket2::Socket>,
            backlog: ::core::ffi::c_int,
        )
        {
            let sqe = &raw mut *self.sqe;

            let fd = socket.as_raw_fd();

            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_listen(sqe, fd, backlog);
            }
        }
    }
}

#[cfg(test)]
pub mod test
{
    use ::assert_fs::TempDir;
    use ::assert_fs::prelude::PathChild as _;

    use crate::IoUring;
    use crate::fd::SlotDesc;
    use crate::sys::SysResult as _;

    #[derive(::bon::Builder)]
    pub struct Fixture<'op>
    {
        #[builder(start_fn)]
        socket: SlotDesc<&'op ::socket2::Socket>,
        #[builder(default = ::libc::SOMAXCONN)]
        backlog: ::core::ffi::c_int,
        #[builder(default = false)]
        sqe_link: bool,
        #[builder(default = false)]
        cqe_skip: bool,
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
                backlog,
                sqe_link,
                cqe_skip,
            } = self;

            let mut sq = ring.squeue();
            let mut sqe = sq
                .get_sqe()
                .ok_or_else(|| ::std::io::Error::other("failed to get sqe"))
                .unwrap();
            unsafe {
                sqe.prep_listen(socket, backlog);
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
            unsafe {
                sqe.set_flags(flags);
            }

            sq.submit().unwrap()
        }

        fn submit_and_wait<S, C>(
            self,
            ring: &mut IoUring<'_, S, C>,
        ) where
            C: crate::cqe::Kind,
            S: crate::sqe::Kind,
        {
            let num = self.submit(ring);
            assert_eq!(1, num);

            let mut cq = ring.cqueue();

            let cqe = cq
                .wait(1)
                .unwrap()
                .next()
                .map(Into::into)
                .ok_or_else(|| ::std::io::Error::other("failed to get cqe"))
                .unwrap();
            cqe.cqe.res.sys_zero().unwrap();
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

    pub fn listen_with<S, C>(
        ring: &mut IoUring<'_, S, C>,
        socket: &SlotDesc<::socket2::Socket>,
        sqe_link: Option<bool>,
        cqe_skip: Option<bool>,
    ) where
        C: crate::cqe::Kind,
        S: crate::sqe::Kind,
    {
        let socket = socket.as_ref();
        crate::sqe::listen::test::Fixture::builder(socket)
            .maybe_sqe_link(sqe_link)
            .maybe_cqe_skip(cqe_skip)
            .build()
            .run(ring);
    }

    #[test]
    fn listen()
    {
        let temp = TempDir::new().map_err(::std::io::Error::other).unwrap();
        let path = temp.child("socket");

        let slots = None;
        let socket_slot = None;

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

        let sqe_link = None;
        let cqe_skip = None;

        crate::sqe::listen::test::listen_with(&mut ring, &socket, sqe_link, cqe_skip);
    }

    #[test]
    fn listen_direct()
    {
        let temp = TempDir::new().map_err(::std::io::Error::other).unwrap();
        let path = temp.child("socket");

        let slots = Some(1);
        let socket_slot = Some(::liburing_rs::IORING_FILE_INDEX_ALLOC.cast_unsigned());

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

        let sqe_link = None;
        let cqe_skip = None;

        crate::sqe::listen::test::listen_with(&mut ring, &socket, sqe_link, cqe_skip);
    }

    #[test]
    fn listen_direct_cqe_skip()
    {
        let temp = TempDir::new().map_err(::std::io::Error::other).unwrap();
        let path = temp.child("socket");

        let slots = Some(1);
        let socket_slot = Some(0);

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

        let sqe_link = None;
        let cqe_skip = Some(true);

        crate::sqe::listen::test::listen_with(&mut ring, &socket, sqe_link, cqe_skip);
    }
}
