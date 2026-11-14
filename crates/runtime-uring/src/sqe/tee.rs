pub mod repr {
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_> {
        pub unsafe fn prep_tee(
            &mut self,
            fd_in: ::core::ffi::c_int,
            fd_out: ::core::ffi::c_int,
            nbytes: ::core::ffi::c_uint,
            splice_flags: ::core::ffi::c_uint,
        ) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_tee(sqe, fd_in, fd_out, nbytes, splice_flags) };
        }
    }
}
