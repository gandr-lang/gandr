//! The preparers of splices between descriptors.

/// The preparers, as methods of the submission entry.
pub mod repr
{
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
            fd_in: ::core::ffi::c_int,
            off_in: i64,
            fd_out: ::core::ffi::c_int,
            off_out: i64,
            nbytes: ::core::ffi::c_uint,
            splice_flags: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
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
