pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        pub unsafe fn prep_ftruncate(
            &mut self,
            fd: ::core::ffi::c_int,
            len: ::core::ffi::c_longlong,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_ftruncate(sqe, fd, len) };
        }
    }
}
