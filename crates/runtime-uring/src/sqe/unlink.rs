//! The preparers of removals of files.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::arg::Fd;
    use crate::arg::Flags;
    use crate::arg::Text;
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for a removal of `path`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `path` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_unlink(
            &mut self,
            Text(path): Text,
            Flags(flags): Flags<::core::ffi::c_int>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_unlink(sqe, path, flags);
            }
        }

        /// Prepares the entry for a removal of `path` under `dfd`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `path` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion.
        ///   `dfd` is an open descriptor, or a slot of the ring's file table
        ///   when the entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_unlinkat(
            &mut self,
            Fd(dfd): Fd,
            Text(path): Text,
            Flags(flags): Flags<::core::ffi::c_int>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_unlinkat(sqe, dfd, path, flags);
            }
        }
    }
}
