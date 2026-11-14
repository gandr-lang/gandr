pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        pub unsafe fn prep_link(
            &mut self,
            oldpath: *const ::core::ffi::c_char,
            newpath: *const ::core::ffi::c_char,
            flags: ::core::ffi::c_int,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_link(sqe, oldpath, newpath, flags) };
        }

        pub unsafe fn prep_link_timeout(
            &mut self,
            ts: *const ::liburing_rs::__kernel_timespec,
            flags: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // FIXME: remove if upstream merges const changes
            let ts = ts.cast_mut();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_link_timeout(sqe, ts, flags) };
        }

        pub unsafe fn prep_linkat(
            &mut self,
            olddfd: ::core::ffi::c_int,
            oldpath: *const ::core::ffi::c_char,
            newdfd: ::core::ffi::c_int,
            newpath: *const ::core::ffi::c_char,
            flags: ::core::ffi::c_int,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_linkat(sqe, olddfd, oldpath, newdfd, newpath, flags)
            };
        }
    }
}
