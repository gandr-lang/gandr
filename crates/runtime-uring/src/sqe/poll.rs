//! The preparers of polls of descriptors.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for a poll of `fd` for the events of `poll_mask`.
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
        pub unsafe fn prep_poll_add(
            &mut self,
            fd: ::core::ffi::c_int,
            poll_mask: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_poll_add(sqe, fd, poll_mask);
            }
        }

        /// Prepares the entry for a poll of `fd` that stays armed and posts one
        /// completion for each event of `poll_mask`.
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
        pub unsafe fn prep_poll_multishot(
            &mut self,
            fd: ::core::ffi::c_int,
            poll_mask: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_poll_multishot(sqe, fd, poll_mask);
            }
        }

        /// Prepares the entry for a removal of the poll whose user data is
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
        pub unsafe fn prep_poll_remove(
            &mut self,
            user_data: u64,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_poll_remove(sqe, user_data);
            }
        }

        /// Prepares the entry for an update of the poll whose user data is
        /// `old_user_data`, to `new_user_data` and the events of `poll_mask`.
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
        pub unsafe fn prep_poll_update(
            &mut self,
            old_user_data: u64,
            new_user_data: u64,
            poll_mask: ::core::ffi::c_uint,
            flags: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_poll_update(
                    sqe,
                    old_user_data,
                    new_user_data,
                    poll_mask,
                    flags,
                );
            }
        }
    }
}
