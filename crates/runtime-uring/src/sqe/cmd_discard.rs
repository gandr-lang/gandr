//! The preparers of discards of ranges of a block device.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::arg::Fd;
    use crate::arg::Len;
    use crate::arg::Offset;
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for a discard of `nbytes` bytes at `offset` of
        /// the block device `fd`.
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
        pub unsafe fn prep_cmd_discard(
            &mut self,
            Fd(fd): Fd,
            Offset(offset): Offset<u64>,
            Len(nbytes): Len<u64>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_cmd_discard(sqe, fd, offset, nbytes);
            }
        }
    }
}
