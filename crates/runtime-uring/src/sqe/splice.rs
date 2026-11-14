pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        #[inline]
        pub unsafe fn prep_splice(
            &mut self,
            fd_in: ::core::ffi::c_int,
            off_in: i64,
            fd_out: ::core::ffi::c_int,
            off_out: i64,
            nbytes: ::core::ffi::c_uint,
            splice_flags: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_splice(
                    sqe,
                    fd_in,
                    off_in,
                    fd_out,
                    off_out,
                    nbytes,
                    splice_flags,
                );
            }
        }
    }
}
