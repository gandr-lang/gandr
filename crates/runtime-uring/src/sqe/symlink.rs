pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        pub unsafe fn prep_symlink(
            &mut self,
            target: *const ::core::ffi::c_char,
            linkpath: *const ::core::ffi::c_char,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_symlink(sqe, target, linkpath) };
        }

        pub unsafe fn prep_symlinkat(
            &mut self,
            target: *const ::core::ffi::c_char,
            newdirfd: ::core::ffi::c_int,
            linkpath: *const ::core::ffi::c_char,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_symlinkat(sqe, target, newdirfd, linkpath) };
        }
    }
}
