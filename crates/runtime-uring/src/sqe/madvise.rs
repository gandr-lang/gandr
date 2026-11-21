//! The preparers of advice on ranges of memory.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::arg::Code;
    use crate::arg::Len;
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for the advice `advice` for `length` bytes of
        /// memory at `addr`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `addr` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_madvise(
            &mut self,
            addr: *mut ::core::ffi::c_void,
            Len(length): Len<u32>,
            Code(advice): Code<::core::ffi::c_int>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_madvise(sqe, addr, length, advice);
            }
        }

        /// Prepares the entry for the advice `advice` for `length` bytes of
        /// memory at `addr`, with a length of 64 bits.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `addr` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_madvise64(
            &mut self,
            addr: *mut ::core::ffi::c_void,
            Len(length): Len<::liburing_rs::off_t>,
            Code(advice): Code<::core::ffi::c_int>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_madvise64(sqe, addr, length, advice);
            }
        }
    }
}
