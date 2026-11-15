//! The preparers of truncates of files.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::arg::Fd;
    use crate::arg::Len;
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for a truncate of `fd` to `len` bytes.
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
        pub unsafe fn prep_ftruncate(
            &mut self,
            Fd(fd): Fd,
            Len(len): Len<::core::ffi::c_longlong>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_ftruncate(sqe, fd, len);
            }
        }
    }
}
