//! The preparers of messages to other rings.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::arg::Fd;
    use crate::arg::Flags;
    use crate::arg::Len;
    use crate::arg::UserData;
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for a message to the ring `fd`, which posts a
        /// completion there with `len` and `data`.
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
        pub unsafe fn prep_msg_ring(
            &mut self,
            Fd(fd): Fd,
            Len(len): Len<::core::ffi::c_uint>,
            UserData(data): UserData,
            Flags(flags): Flags<::core::ffi::c_uint>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_msg_ring(sqe, fd, len, data, flags);
            }
        }

        /// Prepares the entry for a message to the ring `fd`, which posts a
        /// completion there with `len`, `data` and the completion flags
        /// `cqe_flags`.
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
        pub unsafe fn prep_msg_ring_cqe_flags(
            &mut self,
            Fd(fd): Fd,
            Len(len): Len<::core::ffi::c_uint>,
            UserData(data): UserData,
            Flags(flags): Flags<::core::ffi::c_uint>,
            Flags(cqe_flags): Flags<::core::ffi::c_uint>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_msg_ring_cqe_flags(
                    sqe, fd, len, data, flags, cqe_flags,
                );
            }
        }

        /// Prepares the entry for a transfer of the slot `source_fd` of this
        /// ring's file table to the slot `target_fd` of the ring `fd`, with
        /// `data` in the completion.
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
        pub unsafe fn prep_msg_ring_fd(
            &mut self,
            Fd(fd): Fd,
            Fd(source_fd): Fd,
            Fd(target_fd): Fd,
            UserData(data): UserData,
            Flags(flags): Flags<::core::ffi::c_uint>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_msg_ring_fd(
                    sqe, fd, source_fd, target_fd, data, flags,
                );
            }
        }
    }
}
