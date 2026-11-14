pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        #[inline]
        pub unsafe fn prep_rename(
            &mut self,
            oldpath: *const ::core::ffi::c_char,
            newpath: *const ::core::ffi::c_char,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_rename(sqe, oldpath, newpath);
            }
        }

        #[inline]
        pub unsafe fn prep_renameat(
            &mut self,
            olddfd: ::core::ffi::c_int,
            oldpath: *const ::core::ffi::c_char,
            newdfd: ::core::ffi::c_int,
            newpath: *const ::core::ffi::c_char,
            flags: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_renameat(sqe, olddfd, oldpath, newdfd, newpath, flags);
            }
        }
    }
}
