pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        #[inline]
        pub unsafe fn prep_timeout(
            &mut self,
            ts: *const ::liburing_rs::__kernel_timespec,
            count: ::core::ffi::c_uint,
            flags: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // FIXME: remove if upstream merges const changes
            let ts = ts.cast_mut();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_timeout(sqe, ts, count, flags);
            }
        }

        #[inline]
        pub unsafe fn prep_timeout_remove(
            &mut self,
            user_data: u64,
            flags: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_timeout_remove(sqe, user_data, flags);
            }
        }

        #[inline]
        pub unsafe fn prep_timeout_update(
            &mut self,
            ts: *const ::liburing_rs::__kernel_timespec,
            user_data: u64,
            flags: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // FIXME: remove if upstream merges const changes
            let ts = ts.cast_mut();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_timeout_update(sqe, ts, user_data, flags);
            }
        }
    }
}
