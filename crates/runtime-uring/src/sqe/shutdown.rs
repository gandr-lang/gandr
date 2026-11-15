//! The preparers of shutdowns of sockets.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::arg::Code;
    use crate::arg::Fd;
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for a shutdown of the socket `fd` in the
        /// direction `how`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `fd` is an open descriptor, or a slot of the
        ///   ring's file table when the entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_shutdown(
            &mut self,
            Fd(fd): Fd,
            Code(how): Code<::core::ffi::c_int>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_shutdown(sqe, fd, how);
            }
        }
    }
}
