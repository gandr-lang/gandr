pub mod repr {
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_> {
        pub unsafe fn prep_unlink(&mut self, path: *const ::core::ffi::c_char, flags: ::core::ffi::c_int) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_unlink(sqe, path, flags) };
        }

        pub unsafe fn prep_unlinkat(
            &mut self,
            dfd: ::core::ffi::c_int,
            path: *const ::core::ffi::c_char,
            flags: ::core::ffi::c_int,
        ) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_unlinkat(sqe, dfd, path, flags) };
        }
    }
}
