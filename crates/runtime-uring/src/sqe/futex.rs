//! The preparers of waits on futexes and wakes of their waiters.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::arg::Count;
    use crate::arg::Flags;
    use crate::arg::FutexWord;
    use crate::arg::Value;
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for a wait on the futex at `futex` while it holds
        /// `val` under `mask`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `futex` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_futex_wait(
            &mut self,
            FutexWord(futex): FutexWord,
            Value(val): Value,
            Flags(mask): Flags<u64>,
            Flags(futex_flags): Flags<u32>,
            Flags(flags): Flags<::core::ffi::c_uint>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // liburing's signature takes a mutable pointer here, though the
            // kernel only reads it; the cast leaves when liburing
            // takes a constant pointer.
            let futex = futex.cast_mut();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_futex_wait(sqe, futex, val, mask, futex_flags, flags);
            }
        }

        /// Prepares the entry for a wait on the `nr_futex` futexes of the
        /// vector at `futex`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `futex` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_futex_waitv(
            &mut self,
            futex: *const ::liburing_rs::futex_waitv,
            Count(nr_futex): Count<u32>,
            Flags(flags): Flags<::core::ffi::c_uint>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // liburing's signature takes a mutable pointer here, though the
            // kernel only reads it; the cast leaves when liburing
            // takes a constant pointer.
            let futex = futex.cast_mut();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_futex_waitv(sqe, futex, nr_futex, flags);
            }
        }

        /// Prepares the entry for a wake of the waiters on the futex at
        /// `futex`, at most `val` of them, under `mask`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `futex` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_futex_wake(
            &mut self,
            FutexWord(futex): FutexWord,
            Value(val): Value,
            Flags(mask): Flags<u64>,
            Flags(futex_flags): Flags<u32>,
            Flags(flags): Flags<::core::ffi::c_uint>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // liburing's signature takes a mutable pointer here, though the
            // kernel only reads it; the cast leaves when liburing
            // takes a constant pointer.
            let futex = futex.cast_mut();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_futex_wake(sqe, futex, val, mask, futex_flags, flags);
            }
        }
    }
}
