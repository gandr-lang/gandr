//! The preparers of makes of directories.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::arg::Fd;
    use crate::arg::Mode;
    use crate::arg::Text;
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for a make of the directory `path` with the mode
        /// `mode`.
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
        pub unsafe fn prep_mkdir(
            &mut self,
            Text(path): Text,
            Mode(mode): Mode<::liburing_rs::mode_t>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_mkdir(sqe, path, mode);
            }
        }

        /// Prepares the entry for a make of the directory `path` under `dfd`
        /// with the mode `mode`.
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
        pub unsafe fn prep_mkdirat(
            &mut self,
            Fd(dfd): Fd,
            Text(path): Text,
            Mode(mode): Mode<::liburing_rs::mode_t>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_mkdirat(sqe, dfd, path, mode);
            }
        }
    }
}
