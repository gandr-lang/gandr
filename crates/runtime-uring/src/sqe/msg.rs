pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        pub unsafe fn prep_msg_ring(
            &mut self,
            fd: ::core::ffi::c_int,
            len: ::core::ffi::c_uint,
            data: u64,
            flags: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_msg_ring(sqe, fd, len, data, flags) };
        }

        pub unsafe fn prep_msg_ring_cqe_flags(
            &mut self,
            fd: ::core::ffi::c_int,
            len: ::core::ffi::c_uint,
            data: u64,
            flags: ::core::ffi::c_uint,
            cqe_flags: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_msg_ring_cqe_flags(
                    sqe, fd, len, data, flags, cqe_flags,
                )
            };
        }

        pub unsafe fn prep_msg_ring_fd(
            &mut self,
            fd: ::core::ffi::c_int,
            source_fd: ::core::ffi::c_int,
            target_fd: ::core::ffi::c_int,
            data: u64,
            flags: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_msg_ring_fd(sqe, fd, source_fd, target_fd, data, flags)
            };
        }
    }
}
