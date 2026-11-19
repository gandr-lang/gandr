//! The preparers of sockets.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::arg::Index;
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for a socket of `domain`, `type` and `protocol`.
        /// With `file_index` the kernel puts it in that slot of the ring's file
        /// table.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: The owner's crate marks each preparer `unsafe`.
        ///   This one reads no pointer and names no descriptor, so it holds no
        ///   invariant of its own.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_socket(
            &mut self,
            domain: ::socket2::Domain,
            r#type: ::socket2::Type,
            protocol: Option<::socket2::Protocol>,
            flags: ::rustix::net::SocketFlags,
            file_index: Option<Index<::core::ffi::c_uint>>,
        )
        {
            let sqe = &raw mut *self.sqe();
            let domain = domain.into();
            let r#type = r#type.into();
            let protocol = protocol.map_or_default(Into::into);
            let flags = flags.bits();
            if let Some(Index(file_index)) = file_index {
                // SAFETY: The enclosing method preserves the safety interface.
                unsafe {
                    ::liburing_rs::io_uring_prep_socket_direct(
                        sqe, domain, r#type, protocol, file_index, flags,
                    );
                }
            }
            else {
                // SAFETY: The enclosing method preserves the safety interface.
                unsafe {
                    ::liburing_rs::io_uring_prep_socket(sqe, domain, r#type, protocol, flags);
                }
            }
        }
    }
}

#[cfg(test)]
pub mod test
{
    use ::std::os::fd::BorrowedFd;
    use ::std::os::fd::FromRawFd as _;

    use crate::IoUring;
    use crate::arg::Answer;
    use crate::arg::Count;
    use crate::arg::Flags;
    use crate::arg::Index;
    use crate::arg::Switch;
    use crate::fd::SlotDesc;
    use crate::sys::SysResult as _;

    #[derive(::bon::Builder)]
    #[builder(finish_fn(vis = "", name = build_internal))]
    pub struct Fixture<'fds>
    {
        #[builder(start_fn)]
        domain: ::socket2::Domain,
        #[builder(start_fn)]
        r#type: ::socket2::Type,
        protocol: Option<::socket2::Protocol>,
        #[builder(default = ::rustix::net::SocketFlags::empty())]
        flags: ::rustix::net::SocketFlags,

        #[builder(default)]
        files: &'fds [BorrowedFd<'fds>],
        slots: Option<Count<::core::ffi::c_uint>>,
        socket_slot: Option<Index<::core::ffi::c_uint>>,

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

            if let Some(Index(slot)) = this.socket_slot {
                assert!(
                    this.slots.is_some() || !this.files.is_empty(),
                    "file registration must be configured if using slots"
                );
                if slot == ::liburing_rs::IORING_FILE_INDEX_ALLOC.cast_unsigned() {
                    assert!(
                        !this.cqe_skip.0,
                        "cqe skipping unsupported when using auto slot allocation"
                    );
                }
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
                domain,
                r#type,
                protocol,
                flags,
                socket_slot,
                sqe_link,
                cqe_skip,
                files,
                slots,
            } = self;

            // configure sliced file registration
            if !files.is_empty() {
                let slots = slots
                    .map(|Count(slots)| usize::try_from(slots))
                    .and_then(Result::ok)
                    .unwrap_or(files.len());
                let files = &files[.. slots];
                let registrar = ring.registrar();
                registrar.register_files(files).unwrap();
            }
            // configure sparse file registration
            else if let Some(Count(slots)) = slots {
                let slots = usize::try_from(slots).unwrap_or(files.len());
                let registrar = ring.registrar();
                registrar.register_files_sparse(Count(slots)).unwrap();
            }

            // prepare sqe op
            let mut sq = ring.squeue();
            let mut sqe = sq
                .get_sqe()
                .ok_or_else(|| ::std::io::Error::other("failed to get sqe"))
                .unwrap();
            // SAFETY: the entry reads no pointer, and the slot, if any, is in
            // the table that the test registers.
            unsafe {
                sqe.prep_socket(domain, r#type, protocol, flags, socket_slot);
            }

            // prepare sqe flags
            let mut flags = ::core::ffi::c_uint::default();
            if sqe_link.0 {
                flags |= ::liburing_rs::IOSQE_IO_LINK;
            }
            if cqe_skip.0 {
                flags |= ::liburing_rs::IOSQE_CQE_SKIP_SUCCESS;
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
        ) -> SlotDesc<::socket2::Socket>
        where
            C: crate::cqe::Kind,
            S: crate::sqe::Kind,
        {
            let uses_slot = self.socket_slot.is_some();

            let num = self.submit(ring);
            assert_eq!(Count(1), num);

            let mut cq = ring.cqueue();

            let cqe = cq.wait(Count(1)).unwrap().next();
            let cqe = cqe
                .map(Into::<crate::Cqe16<'_>>::into)
                .ok_or_else(|| ::std::io::Error::other("failed to get cqe"))
                .unwrap();
            let Answer(desc) = Answer(cqe.cqe().res).sys_uint().unwrap();

            if uses_slot {
                SlotDesc::Slot(desc)
            }
            else {
                let fd = desc.cast_signed();
                // SAFETY: the completion gives a new descriptor, which this
                // socket owns alone from here.
                unsafe { ::socket2::Socket::from_raw_fd(fd) }.into()
            }
        }

        /// Runs the fixture on `ring` and checks the outcome.
        ///
        /// # Specification
        ///
        /// trivial.
        #[must_use]
        pub fn run<S, C>(
            self,
            ring: &mut IoUring<'_, S, C>,
        ) -> SlotDesc<::socket2::Socket>
        where
            C: crate::cqe::Kind,
            S: crate::sqe::Kind,
        {
            if self.cqe_skip.0 {
                let Index(slot) = self
                    .socket_slot
                    .ok_or_else(|| {
                        ::std::io::Error::other(
                            "using `cqe_skip` requires specifying `socket_slot`",
                        )
                    })
                    .unwrap();
                self.submit(ring);
                SlotDesc::Slot(slot)
            }
            else {
                self.submit_and_wait(ring)
            }
        }
    }

    /// Runs the socket fixture on `ring` with these arguments.
    ///
    /// # Specification
    ///
    /// trivial.
    pub fn socket_with<S, C>(
        ring: &mut IoUring<'_, S, C>,
        slots: Option<Count<::core::ffi::c_uint>>,
        socket_slot: Option<Index<::core::ffi::c_uint>>,
        sqe_link: Option<Switch>,
        cqe_skip: Option<Switch>,
    ) -> SlotDesc<::socket2::Socket>
    where
        C: crate::cqe::Kind,
        S: crate::sqe::Kind,
    {
        let domain = ::socket2::Domain::UNIX;
        let r#type = ::socket2::Type::STREAM;

        let desc = crate::sqe::socket::test::Fixture::builder(domain, r#type)
            .maybe_slots(slots)
            .maybe_socket_slot(socket_slot)
            .maybe_sqe_link(sqe_link)
            .maybe_cqe_skip(cqe_skip)
            .build()
            .run(ring);

        if socket_slot.is_some() {
            assert!(desc.is_slot().0);
        }
        else {
            assert!(desc.is_desc().0);
        }

        desc
    }

    #[test]
    #[cfg_attr(
        miri,
        ignore = "it sets up a ring through liburing, which Miri cannot run"
    )]
    fn socket()
    {
        let slots = None;
        let socket_slot = None;

        let mut ring = IoUring::new().unwrap();

        let sqe_link = None;
        let cqe_skip = None;

        crate::sqe::socket::test::socket_with(&mut ring, slots, socket_slot, sqe_link, cqe_skip);
    }

    #[test]
    #[cfg_attr(
        miri,
        ignore = "it sets up a ring through liburing, which Miri cannot run"
    )]
    fn socket_direct()
    {
        let slots = Some(Count(1));
        let socket_slot = Some(Index(
            ::liburing_rs::IORING_FILE_INDEX_ALLOC.cast_unsigned(),
        ));

        let mut ring = IoUring::new().unwrap();

        let sqe_link = None;
        let cqe_skip = None;

        crate::sqe::socket::test::socket_with(&mut ring, slots, socket_slot, sqe_link, cqe_skip);
    }

    #[test]
    #[cfg_attr(
        miri,
        ignore = "it sets up a ring through liburing, which Miri cannot run"
    )]
    fn socket_direct_cqe_skip()
    {
        let slots = Some(Count(1));
        let socket_slot = Some(Index(0));

        let mut ring = IoUring::new().unwrap();

        let sqe_link = None;
        let cqe_skip = Some(Switch(true));

        crate::sqe::socket::test::socket_with(&mut ring, slots, socket_slot, sqe_link, cqe_skip);
    }
}
