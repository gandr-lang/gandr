pub mod repr {
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_> {
        pub unsafe fn prep_cancel(&mut self, user_data: *const ::core::ffi::c_void, flags: ::core::ffi::c_int) {
            let sqe = &raw mut *self.sqe;
            // FIXME: remove if upstream merges const changes
            let user_data = user_data.cast_mut();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_cancel(sqe, user_data, flags) };
        }

        pub unsafe fn prep_cancel64(&mut self, user_data: u64, flags: ::core::ffi::c_int) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_cancel64(sqe, user_data, flags) };
        }

        pub unsafe fn prep_cancel_fd(&mut self, fd: ::core::ffi::c_int, flags: ::core::ffi::c_uint) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_cancel_fd(sqe, fd, flags) };
        }
    }
}
