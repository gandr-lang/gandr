//! The preparers of timeouts.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for a timeout of `ts`, or of `count` completions
        /// when `count` is not zero.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `ts` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_timeout(
            &mut self,
            ts: *const ::liburing_rs::__kernel_timespec,
            count: ::core::ffi::c_uint,
            flags: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // liburing's signature takes a mutable pointer here, though the
            // kernel only reads it; the cast leaves when liburing
            // takes a constant pointer.
            let ts = ts.cast_mut();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_timeout(sqe, ts, count, flags);
            }
        }

        /// Prepares the entry for a removal of the timeout whose user data is
        /// `user_data`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: The owner's crate marks each preparer `unsafe`.
        ///   This one reads no pointer and names no descriptor, so it holds no
        ///   invariant of its own.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_timeout_remove(
            &mut self,
            user_data: u64,
            flags: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_timeout_remove(sqe, user_data, flags);
            }
        }

        /// Prepares the entry for an update of the timeout whose user data is
        /// `user_data` to `ts`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `ts` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_timeout_update(
            &mut self,
            ts: *const ::liburing_rs::__kernel_timespec,
            user_data: u64,
            flags: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // liburing's signature takes a mutable pointer here, though the
            // kernel only reads it; the cast leaves when liburing
            // takes a constant pointer.
            let ts = ts.cast_mut();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_timeout_update(sqe, ts, user_data, flags);
            }
        }
    }
}
