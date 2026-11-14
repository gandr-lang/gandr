pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        #[inline]
        pub unsafe fn prep_cmd_discard(
            &mut self,
            fd: ::core::ffi::c_int,
            offset: u64,
            nbytes: u64,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_cmd_discard(sqe, fd, offset, nbytes);
            }
        }
    }
}
