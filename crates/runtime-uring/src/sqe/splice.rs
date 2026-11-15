//! The preparers of splices between descriptors.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::arg::Fd;
    use crate::arg::Flags;
    use crate::arg::Len;
    use crate::arg::Offset;
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for a splice of `nbytes` bytes from `fd_in` at
        /// `off_in` to `fd_out` at `off_out`.
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
        pub unsafe fn prep_splice(
            &mut self,
            Fd(fd_in): Fd,
            Offset(off_in): Offset<i64>,
            Fd(fd_out): Fd,
            Offset(off_out): Offset<i64>,
            Len(nbytes): Len<::core::ffi::c_uint>,
            Flags(splice_flags): Flags<::core::ffi::c_uint>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_splice(
                    sqe,
                    fd_in,
                    off_in,
                    fd_out,
                    off_out,
                    nbytes,
                    splice_flags,
                );
            }
        }
    }
}
