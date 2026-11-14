pub mod repr {
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_> {
        pub unsafe fn prep_connect(
            &mut self,
            fd: ::core::ffi::c_int,
            addr: *const ::liburing_rs::sockaddr,
            addrlen: ::liburing_rs::socklen_t,
        ) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_connect(sqe, fd, addr, addrlen) };
        }
    }
}
