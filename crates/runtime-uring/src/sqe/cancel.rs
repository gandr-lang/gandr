//! The preparers of cancels of entries.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::arg::Fd;
    use crate::arg::Flags;
    use crate::arg::UserData;
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for a cancel of the entry whose user data is the
        /// pointer `user_data`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `user_data` points to memory that stays valid,
        ///   and does not move, until the kernel posts the entry's completion.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_cancel(
            &mut self,
            user_data: *const ::core::ffi::c_void,
            Flags(flags): Flags<::core::ffi::c_int>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // liburing's signature takes a mutable pointer here, though the
            // kernel only reads it; the cast leaves when liburing
            // takes a constant pointer.
            let user_data = user_data.cast_mut();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_cancel(sqe, user_data, flags);
            }
        }

        /// Prepares the entry for a cancel of the entry whose user data is
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
        pub unsafe fn prep_cancel64(
            &mut self,
            UserData(user_data): UserData,
            Flags(flags): Flags<::core::ffi::c_int>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_cancel64(sqe, user_data, flags);
            }
        }

        /// Prepares the entry for a cancel of the entries that operate on `fd`.
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
        pub unsafe fn prep_cancel_fd(
            &mut self,
            Fd(fd): Fd,
            Flags(flags): Flags<::core::ffi::c_uint>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_cancel_fd(sqe, fd, flags);
            }
        }
    }
}
