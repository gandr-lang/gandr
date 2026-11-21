//! The preparers of pipes.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::arg::Fds;
    use crate::arg::Flags;
    use crate::arg::Index;
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
            Fds(fds): Fds<*mut ::core::ffi::c_int>,
            Flags(pipe_flags): Flags<::core::ffi::c_int>,
        )
        {
            let sqe = &raw mut *self.sqe();
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
            Fds(fds): Fds<*mut ::core::ffi::c_int>,
            Flags(pipe_flags): Flags<::core::ffi::c_int>,
            Index(file_index): Index<::core::ffi::c_uint>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_pipe_direct(sqe, fds, pipe_flags, file_index);
            }
        }
    }
}
