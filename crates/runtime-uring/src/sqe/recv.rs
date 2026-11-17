//! The preparers of receives on sockets.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::arg::Fd;
    use crate::arg::Flags;
    use crate::arg::Len;
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for a receive of at most `len` bytes from
        /// `sockfd` into `buf`.
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
        pub unsafe fn prep_recv(
            &mut self,
            Fd(sockfd): Fd,
            buf: *mut ::core::ffi::c_void,
            Len(len): Len<usize>,
            Flags(flags): Flags<::core::ffi::c_int>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_recv(sqe, sockfd, buf, len, flags);
            }
        }

        /// Prepares the entry for a receive from `sockfd` that stays armed and
        /// posts one completion for each message.
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
        pub unsafe fn prep_recv_multishot(
            &mut self,
            Fd(sockfd): Fd,
            buf: *mut ::core::ffi::c_void,
            Len(len): Len<usize>,
            Flags(flags): Flags<::core::ffi::c_int>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_recv_multishot(sqe, sockfd, buf, len, flags);
            }
        }

        /// Prepares the entry for a receive of one message from `fd` into the
        /// header at `msg`.
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
        pub unsafe fn prep_recvmsg(
            &mut self,
            Fd(fd): Fd,
            msg: *mut ::liburing_rs::msghdr,
            Flags(flags): Flags<::core::ffi::c_uint>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_recvmsg(sqe, fd, msg, flags);
            }
        }

        /// Prepares the entry for a receive from `fd` that stays armed, with
        /// the header at `msg` as its template.
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
        pub unsafe fn prep_recvmsg_multishot(
            &mut self,
            Fd(fd): Fd,
            msg: *mut ::liburing_rs::msghdr,
            Flags(flags): Flags<::core::ffi::c_uint>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_recvmsg_multishot(sqe, fd, msg, flags);
            }
        }
    }
}
