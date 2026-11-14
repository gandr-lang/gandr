pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        pub unsafe fn prep_mkdir(
            &mut self,
            path: *const ::core::ffi::c_char,
            mode: ::liburing_rs::mode_t,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_mkdir(sqe, path, mode) };
        }

        pub unsafe fn prep_mkdirat(
            &mut self,
            dfd: ::core::ffi::c_int,
            path: *const ::core::ffi::c_char,
            mode: ::liburing_rs::mode_t,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_mkdirat(sqe, dfd, path, mode) };
        }
    }
}
