pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        #[inline]
        pub unsafe fn prep_poll_add(
            &mut self,
            fd: ::core::ffi::c_int,
            poll_mask: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_poll_add(sqe, fd, poll_mask);
            }
        }

        #[inline]
        pub unsafe fn prep_poll_multishot(
            &mut self,
            fd: ::core::ffi::c_int,
            poll_mask: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_poll_multishot(sqe, fd, poll_mask);
            }
        }

        #[inline]
        pub unsafe fn prep_poll_remove(
            &mut self,
            user_data: u64,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_poll_remove(sqe, user_data);
            }
        }

        #[inline]
        pub unsafe fn prep_poll_update(
            &mut self,
            old_user_data: u64,
            new_user_data: u64,
            poll_mask: ::core::ffi::c_uint,
            flags: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_poll_update(
                    sqe,
                    old_user_data,
                    new_user_data,
                    poll_mask,
                    flags,
                );
            }
        }
    }
}
