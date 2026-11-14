pub mod repr {
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_> {
        pub unsafe fn prep_open(
            &mut self,
            path: *const ::core::ffi::c_char,
            flags: ::core::ffi::c_int,
            mode: ::liburing_rs::mode_t,
        ) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_open(sqe, path, flags, mode) };
        }

        pub unsafe fn prep_open_direct(
            &mut self,
            path: *const ::core::ffi::c_char,
            flags: ::core::ffi::c_int,
            mode: ::liburing_rs::mode_t,
            file_index: ::core::ffi::c_uint,
        ) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_open_direct(sqe, path, flags, mode, file_index) };
        }

        pub unsafe fn prep_openat(
            &mut self,
            dfd: ::core::ffi::c_int,
            path: *const ::core::ffi::c_char,
            flags: ::core::ffi::c_int,
            mode: ::liburing_rs::mode_t,
        ) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_openat(sqe, dfd, path, flags, mode) };
        }

        pub unsafe fn prep_openat2(
            &mut self,
            dfd: ::core::ffi::c_int,
            path: *const ::core::ffi::c_char,
            how: *const ::liburing_rs::open_how,
        ) {
            let sqe = &raw mut *self.sqe;
            // FIXME: remove if upstream merges const changes
            let how = how.cast_mut();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_openat2(sqe, dfd, path, how) };
        }

        pub unsafe fn prep_openat2_direct(
            &mut self,
            dfd: ::core::ffi::c_int,
            path: *const ::core::ffi::c_char,
            how: *const ::liburing_rs::open_how,
            file_index: ::core::ffi::c_uint,
        ) {
            let sqe = &raw mut *self.sqe;
            // FIXME: remove if upstream merges const changes
            let how = how.cast_mut();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_openat2_direct(sqe, dfd, path, how, file_index) };
        }

        pub unsafe fn prep_openat_direct(
            &mut self,
            dfd: ::core::ffi::c_int,
            path: *const ::core::ffi::c_char,
            flags: ::core::ffi::c_int,
            mode: ::liburing_rs::mode_t,
            file_index: ::core::ffi::c_uint,
        ) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_openat_direct(sqe, dfd, path, flags, mode, file_index) };
        }
    }
}
