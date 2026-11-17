//! The preparers of symbolic links.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::arg::Fd;
    use crate::arg::Text;
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for a symbolic link at `linkpath` to `target`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `target` and `linkpath` point to memory that
        ///   stays valid, and does not move, until the kernel posts the entry's
        ///   completion.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_symlink(
            &mut self,
            Text(target): Text,
            Text(linkpath): Text,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_symlink(sqe, target, linkpath);
            }
        }

        /// Prepares the entry for a symbolic link at `linkpath` under
        /// `newdirfd` to `target`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `target` and `linkpath` point to memory that
        ///   stays valid, and does not move, until the kernel posts the entry's
        ///   completion. `newdirfd` is an open descriptor, or a slot of the
        ///   ring's file table when the entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_symlinkat(
            &mut self,
            Text(target): Text,
            Fd(newdirfd): Fd,
            Text(linkpath): Text,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_symlinkat(sqe, target, newdirfd, linkpath);
            }
        }
    }
}
