//! The preparers of pipes.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for a pipe whose two descriptors the kernel
        /// writes to `fds`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `fds` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_pipe(
            &mut self,
            fds: *mut ::core::ffi::c_int,
            pipe_flags: ::core::ffi::c_int,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_pipe(sqe, fds, pipe_flags);
            }
        }

        /// Prepares the entry for a pipe whose two ends go to the ring's file
        /// table from the slot `file_index`, with the slots written to `fds`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `fds` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_pipe_direct(
            &mut self,
            fds: *mut ::core::ffi::c_int,
            pipe_flags: ::core::ffi::c_int,
            file_index: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_pipe_direct(sqe, fds, pipe_flags, file_index);
            }
        }
    }
}
