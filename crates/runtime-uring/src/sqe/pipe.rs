pub mod repr {
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_> {
        pub unsafe fn prep_pipe(&mut self, fds: *mut ::core::ffi::c_int, pipe_flags: ::core::ffi::c_int) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_pipe(sqe, fds, pipe_flags) };
        }

        pub unsafe fn prep_pipe_direct(
            &mut self,
            fds: *mut ::core::ffi::c_int,
            pipe_flags: ::core::ffi::c_int,
            file_index: ::core::ffi::c_uint,
        ) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_pipe_direct(sqe, fds, pipe_flags, file_index) };
        }
    }
}
