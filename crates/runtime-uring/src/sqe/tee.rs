//! The preparers of copies between pipes.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::arg::Fd;
    use crate::arg::Flags;
    use crate::arg::Len;
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for a copy of `nbytes` bytes from the pipe
        /// `fd_in` to the pipe `fd_out`, with no read of the bytes.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `fd_in` and `fd_out` are open descriptors, or
        ///   slots of the ring's file table when the entry carries the
        ///   fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_tee(
            &mut self,
            Fd(fd_in): Fd,
            Fd(fd_out): Fd,
            Len(nbytes): Len<::core::ffi::c_uint>,
            Flags(splice_flags): Flags<::core::ffi::c_uint>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_tee(sqe, fd_in, fd_out, nbytes, splice_flags);
            }
        }
    }
}
