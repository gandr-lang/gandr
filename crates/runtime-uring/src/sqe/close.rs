//! The preparers of closes of descriptors and slots.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::arg::Fd;
    use crate::arg::Index;
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for a close of `fd`.
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
        pub unsafe fn prep_close(
            &mut self,
            Fd(fd): Fd,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_close(sqe, fd);
            }
        }

        /// Prepares the entry for a close of the slot `file_index` of the
        /// ring's file table.
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
        pub unsafe fn prep_close_direct(
            &mut self,
            Index(file_index): Index<::core::ffi::c_uint>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_close_direct(sqe, file_index);
            }
        }
    }
}
