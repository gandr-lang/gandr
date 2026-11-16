//! The preparers of socket commands.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::arg::Code;
    use crate::arg::Fd;
    use crate::arg::Len;
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for the socket command `cmd_op` on `fd`, for the
        /// option `optname` at `level`, with its value at `optval`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `optval` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion. `fd`
        ///   is an open descriptor, or a slot of the ring's file table when the
        ///   entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_cmd_sock(
            &mut self,
            Code(cmd_op): Code<::core::ffi::c_int>,
            Fd(fd): Fd,
            Code(level): Code<::core::ffi::c_int>,
            Code(optname): Code<::core::ffi::c_int>,
            optval: *mut ::core::ffi::c_void,
            Len(optlen): Len<::core::ffi::c_int>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_cmd_sock(
                    sqe, cmd_op, fd, level, optname, optval, optlen,
                );
            }
        }
    }
}
