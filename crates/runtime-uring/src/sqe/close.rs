pub mod repr {
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_> {
        pub unsafe fn prep_close(&mut self, fd: ::core::ffi::c_int) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_close(sqe, fd) };
        }

        pub unsafe fn prep_close_direct(&mut self, file_index: ::core::ffi::c_uint) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_close_direct(sqe, file_index) };
        }
    }
}
