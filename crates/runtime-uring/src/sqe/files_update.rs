//! The preparers of updates of the ring's file table.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::arg::Count;
    use crate::arg::Fds;
    use crate::arg::Index;
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for an update of the ring's file table from slot
        /// `offset` with the `nr_fds` descriptors at `fds`.
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
        pub unsafe fn prep_files_update(
            &mut self,
            Fds(fds): Fds<*const ::core::ffi::c_int>,
            Count(nr_fds): Count<::core::ffi::c_uint>,
            Index(offset): Index<::core::ffi::c_int>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // liburing's signature takes a mutable pointer here, though the
            // kernel only reads it; the cast leaves when liburing
            // takes a constant pointer.
            let fds = fds.cast_mut();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_files_update(sqe, fds, nr_fds, offset);
            }
        }
    }
}
