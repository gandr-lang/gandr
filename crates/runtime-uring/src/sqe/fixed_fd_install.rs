//! The preparers of installs of slots as descriptors of the process.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for an install of the slot `fd` of the ring's
        /// file table as a normal descriptor of the process.
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
        pub unsafe fn prep_fixed_fd_install(
            &mut self,
            fd: ::core::ffi::c_int,
            flags: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_fixed_fd_install(sqe, fd, flags);
            }
        }
    }
}
