//! The preparers of status reads of files.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::arg::Fd;
    use crate::arg::Flags;
    use crate::arg::Text;
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for a status read of `path` under `dfd` for the
        /// fields of `mask`, written to `statxbuf`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `path` and `statxbuf` point to memory that
        ///   stays valid, and does not move, until the kernel posts the entry's
        ///   completion. `dfd` is an open descriptor, or a slot of the ring's
        ///   file table when the entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_statx(
            &mut self,
            Fd(dfd): Fd,
            Text(path): Text,
            Flags(flags): Flags<::core::ffi::c_int>,
            Flags(mask): Flags<::core::ffi::c_uint>,
            statxbuf: *mut ::liburing_rs::statx,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_statx(sqe, dfd, path, flags, mask, statxbuf);
            }
        }
    }
}
