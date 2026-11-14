pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        #[inline]
        pub unsafe fn prep_recv(
            &mut self,
            sockfd: ::core::ffi::c_int,
            buf: *mut ::core::ffi::c_void,
            len: usize,
            flags: ::core::ffi::c_int,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_recv(sqe, sockfd, buf, len, flags);
            }
        }

        #[inline]
        pub unsafe fn prep_recv_multishot(
            &mut self,
            sockfd: ::core::ffi::c_int,
            buf: *mut ::core::ffi::c_void,
            len: usize,
            flags: ::core::ffi::c_int,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_recv_multishot(sqe, sockfd, buf, len, flags);
            }
        }

        #[inline]
        pub unsafe fn prep_recvmsg(
            &mut self,
            fd: ::core::ffi::c_int,
            msg: *mut ::liburing_rs::msghdr,
            flags: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_recvmsg(sqe, fd, msg, flags);
            }
        }

        #[inline]
        pub unsafe fn prep_recvmsg_multishot(
            &mut self,
            fd: ::core::ffi::c_int,
            msg: *mut ::liburing_rs::msghdr,
            flags: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_recvmsg_multishot(sqe, fd, msg, flags);
            }
        }
    }
}
