//! The preparers of allocations of ranges of a file.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for an allocation of `len` bytes at `offset` of
        /// `fd` in the mode `mode`.
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
        pub unsafe fn prep_fallocate(
            &mut self,
            fd: ::core::ffi::c_int,
            mode: ::core::ffi::c_int,
            offset: u64,
            len: u64,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_fallocate(sqe, fd, mode, offset, len);
            }
        }
    }
}
