pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        pub unsafe fn prep_fadvise(
            &mut self,
            fd: ::core::ffi::c_int,
            offset: u64,
            len: u32,
            advice: ::core::ffi::c_int,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_fadvise(sqe, fd, offset, len, advice) };
        }

        pub unsafe fn prep_fadvise64(
            &mut self,
            fd: ::core::ffi::c_int,
            offset: u64,
            len: ::liburing_rs::off_t,
            advice: ::core::ffi::c_int,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_fadvise64(sqe, fd, offset, len, advice) };
        }
    }
}
