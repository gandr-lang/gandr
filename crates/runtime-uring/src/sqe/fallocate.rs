pub mod repr {
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_> {
        pub unsafe fn prep_fallocate(
            &mut self,
            fd: ::core::ffi::c_int,
            mode: ::core::ffi::c_int,
            offset: u64,
            len: u64,
        ) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_fallocate(sqe, fd, mode, offset, len) };
        }
    }
}
