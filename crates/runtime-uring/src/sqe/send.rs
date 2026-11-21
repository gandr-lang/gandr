//! The preparers of sends on sockets.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::arg::Fd;
    use crate::arg::Flags;
    use crate::arg::Index;
    use crate::arg::Len;
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for a send of `len` bytes at `buf` on `sockfd`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `buf` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion.
        ///   `sockfd` is an open descriptor, or a slot of the ring's file table
        ///   when the entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_send(
            &mut self,
            Fd(sockfd): Fd,
            buf: *const ::core::ffi::c_void,
            Len(len): Len<usize>,
            Flags(flags): Flags<::core::ffi::c_int>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_send(sqe, sockfd, buf, len, flags);
            }
        }

        /// Prepares the entry for a send of at most `len` bytes on `sockfd`
        /// from the buffers of the entry's buffer group.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `sockfd` is an open descriptor, or a slot of
        ///   the ring's file table when the entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_send_bundle(
            &mut self,
            Fd(sockfd): Fd,
            Len(len): Len<usize>,
            Flags(flags): Flags<::core::ffi::c_int>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_send_bundle(sqe, sockfd, len, flags);
            }
        }

        /// Prepares the entry for the destination address `dest_addr` for the
        /// send of this entry.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `dest_addr` points to memory that stays valid,
        ///   and does not move, until the kernel posts the entry's completion.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_send_set_addr(
            &mut self,
            dest_addr: *const ::liburing_rs::sockaddr,
            Len(addr_len): Len<u16>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_send_set_addr(sqe, dest_addr, addr_len);
            }
        }

        /// Prepares the entry for a send of `len` bytes at `buf` on `sockfd`
        /// with no copy.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `buf` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion.
        ///   `sockfd` is an open descriptor, or a slot of the ring's file table
        ///   when the entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_send_zc(
            &mut self,
            Fd(sockfd): Fd,
            buf: *const ::core::ffi::c_void,
            Len(len): Len<usize>,
            Flags(flags): Flags<::core::ffi::c_int>,
            Flags(zc_flags): Flags<::core::ffi::c_uint>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_send_zc(sqe, sockfd, buf, len, flags, zc_flags);
            }
        }

        /// Prepares the entry for a send of `len` bytes at `buf`, a registered
        /// buffer of index `buf_index`, on `sockfd` with no copy.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `buf` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion.
        ///   `sockfd` is an open descriptor, or a slot of the ring's file table
        ///   when the entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_send_zc_fixed(
            &mut self,
            Fd(sockfd): Fd,
            buf: *const ::core::ffi::c_void,
            Len(len): Len<usize>,
            Flags(flags): Flags<::core::ffi::c_int>,
            Flags(zc_flags): Flags<::core::ffi::c_uint>,
            Index(buf_index): Index<::core::ffi::c_uint>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_send_zc_fixed(
                    sqe, sockfd, buf, len, flags, zc_flags, buf_index,
                );
            }
        }

        /// Prepares the entry for a send of the message at `msg` on `fd`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `msg` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion. `fd`
        ///   is an open descriptor, or a slot of the ring's file table when the
        ///   entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_sendmsg(
            &mut self,
            Fd(fd): Fd,
            msg: *const ::liburing_rs::msghdr,
            Flags(flags): Flags<::core::ffi::c_uint>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_sendmsg(sqe, fd, msg, flags);
            }
        }

        /// Prepares the entry for a send of the message at `msg` on `fd` with
        /// no copy.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `msg` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion. `fd`
        ///   is an open descriptor, or a slot of the ring's file table when the
        ///   entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_sendmsg_zc(
            &mut self,
            Fd(fd): Fd,
            msg: *const ::liburing_rs::msghdr,
            Flags(flags): Flags<::core::ffi::c_uint>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_sendmsg_zc(sqe, fd, msg, flags);
            }
        }

        /// Prepares the entry for a send of the message at `msg` on `fd` with
        /// no copy, from the registered buffer of index `buf_index`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `msg` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion. `fd`
        ///   is an open descriptor, or a slot of the ring's file table when the
        ///   entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_sendmsg_zc_fixed(
            &mut self,
            Fd(fd): Fd,
            msg: *const ::liburing_rs::msghdr,
            Flags(flags): Flags<::core::ffi::c_uint>,
            Index(buf_index): Index<::core::ffi::c_uint>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_sendmsg_zc_fixed(sqe, fd, msg, flags, buf_index);
            }
        }

        /// Prepares the entry for a send of `len` bytes at `buf` on `sockfd` to
        /// the address `addr`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `buf` and `addr` point to memory that stays
        ///   valid, and does not move, until the kernel posts the entry's
        ///   completion. `sockfd` is an open descriptor, or a slot of the
        ///   ring's file table when the entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_sendto(
            &mut self,
            Fd(sockfd): Fd,
            buf: *const ::core::ffi::c_void,
            Len(len): Len<usize>,
            Flags(flags): Flags<::core::ffi::c_int>,
            addr: *const ::liburing_rs::sockaddr,
            Len(addrlen): Len<::liburing_rs::socklen_t>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_sendto(sqe, sockfd, buf, len, flags, addr, addrlen);
            }
        }
    }
}
