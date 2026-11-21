//! The preparers of connects of sockets.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::arg::Fd;
    use crate::arg::Len;
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for a connect of the socket `fd` to `addr`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `addr` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion. `fd`
        ///   is an open descriptor, or a slot of the ring's file table when the
        ///   entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_connect(
            &mut self,
            Fd(fd): Fd,
            addr: *const ::liburing_rs::sockaddr,
            Len(addrlen): Len<::liburing_rs::socklen_t>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_connect(sqe, fd, addr, addrlen);
            }
        }
    }
}
