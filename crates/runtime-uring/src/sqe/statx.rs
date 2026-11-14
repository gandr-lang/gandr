pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        #[inline]
        pub unsafe fn prep_statx(
            &mut self,
            dfd: ::core::ffi::c_int,
            path: *const ::core::ffi::c_char,
            flags: ::core::ffi::c_int,
            mask: ::core::ffi::c_uint,
            statxbuf: *mut ::liburing_rs::statx,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_statx(sqe, dfd, path, flags, mask, statxbuf);
            }
        }
    }
}
