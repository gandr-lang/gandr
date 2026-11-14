pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        #[inline]
        pub unsafe fn prep_send(
            &mut self,
            sockfd: ::core::ffi::c_int,
            buf: *const ::core::ffi::c_void,
            len: usize,
            flags: ::core::ffi::c_int,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_send(sqe, sockfd, buf, len, flags);
            }
        }

        #[inline]
        pub unsafe fn prep_send_bundle(
            &mut self,
            sockfd: ::core::ffi::c_int,
            len: usize,
            flags: ::core::ffi::c_int,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_send_bundle(sqe, sockfd, len, flags);
            }
        }

        #[inline]
        pub unsafe fn prep_send_set_addr(
            &mut self,
            dest_addr: *const ::liburing_rs::sockaddr,
            addr_len: u16,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_send_set_addr(sqe, dest_addr, addr_len);
            }
        }

        #[inline]
        pub unsafe fn prep_send_zc(
            &mut self,
            sockfd: ::core::ffi::c_int,
            buf: *const ::core::ffi::c_void,
            len: usize,
            flags: ::core::ffi::c_int,
            zc_flags: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_send_zc(sqe, sockfd, buf, len, flags, zc_flags);
            }
        }

        #[inline]
        pub unsafe fn prep_send_zc_fixed(
            &mut self,
            sockfd: ::core::ffi::c_int,
            buf: *const ::core::ffi::c_void,
            len: usize,
            flags: ::core::ffi::c_int,
            zc_flags: ::core::ffi::c_uint,
            buf_index: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_send_zc_fixed(
                    sqe, sockfd, buf, len, flags, zc_flags, buf_index,
                );
            }
        }

        #[inline]
        pub unsafe fn prep_sendmsg(
            &mut self,
            fd: ::core::ffi::c_int,
            msg: *const ::liburing_rs::msghdr,
            flags: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_sendmsg(sqe, fd, msg, flags);
            }
        }

        #[inline]
        pub unsafe fn prep_sendmsg_zc(
            &mut self,
            fd: ::core::ffi::c_int,
            msg: *const ::liburing_rs::msghdr,
            flags: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_sendmsg_zc(sqe, fd, msg, flags);
            }
        }

        #[inline]
        pub unsafe fn prep_sendmsg_zc_fixed(
            &mut self,
            fd: ::core::ffi::c_int,
            msg: *const ::liburing_rs::msghdr,
            flags: ::core::ffi::c_uint,
            buf_index: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_sendmsg_zc_fixed(sqe, fd, msg, flags, buf_index);
            }
        }

        #[inline]
        pub unsafe fn prep_sendto(
            &mut self,
            sockfd: ::core::ffi::c_int,
            buf: *const ::core::ffi::c_void,
            len: usize,
            flags: ::core::ffi::c_int,
            addr: *const ::liburing_rs::sockaddr,
            addrlen: ::liburing_rs::socklen_t,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_sendto(sqe, sockfd, buf, len, flags, addr, addrlen);
            }
        }
    }
}
