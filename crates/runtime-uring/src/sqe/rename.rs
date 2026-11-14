//! The preparers of renames of files.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for a rename of `oldpath` to `newpath`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `oldpath` and `newpath` point to memory that
        ///   stays valid, and does not move, until the kernel posts the entry's
        ///   completion.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_rename(
            &mut self,
            oldpath: *const ::core::ffi::c_char,
            newpath: *const ::core::ffi::c_char,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_rename(sqe, oldpath, newpath);
            }
        }

        /// Prepares the entry for a rename of `oldpath` under `olddfd` to
        /// `newpath` under `newdfd`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `oldpath` and `newpath` point to memory that
        ///   stays valid, and does not move, until the kernel posts the entry's
        ///   completion. `olddfd` and `newdfd` are open descriptors, or slots
        ///   of the ring's file table when the entry carries the fixed-file
        ///   flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_renameat(
            &mut self,
            olddfd: ::core::ffi::c_int,
            oldpath: *const ::core::ffi::c_char,
            newdfd: ::core::ffi::c_int,
            newpath: *const ::core::ffi::c_char,
            flags: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_renameat(sqe, olddfd, oldpath, newdfd, newpath, flags);
            }
        }
    }
}
