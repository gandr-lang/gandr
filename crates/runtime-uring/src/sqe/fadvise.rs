//! The preparers of advice on ranges of a file.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::arg::Code;
    use crate::arg::Fd;
    use crate::arg::Len;
    use crate::arg::Offset;
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for the advice `advice` for `len` bytes at
        /// `offset` of `fd`.
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
        pub unsafe fn prep_fadvise(
            &mut self,
            Fd(fd): Fd,
            Offset(offset): Offset<u64>,
            Len(len): Len<u32>,
            Code(advice): Code<::core::ffi::c_int>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_fadvise(sqe, fd, offset, len, advice);
            }
        }

        /// Prepares the entry for the advice `advice` for `len` bytes at
        /// `offset` of `fd`, with a length of 64 bits.
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
        pub unsafe fn prep_fadvise64(
            &mut self,
            Fd(fd): Fd,
            Offset(offset): Offset<u64>,
            Len(len): Len<::liburing_rs::off_t>,
            Code(advice): Code<::core::ffi::c_int>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_fadvise64(sqe, fd, offset, len, advice);
            }
        }
    }
}
