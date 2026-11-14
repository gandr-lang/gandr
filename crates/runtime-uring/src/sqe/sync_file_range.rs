pub mod repr {
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_> {
        pub unsafe fn prep_sync_file_range(
            &mut self,
            fd: ::core::ffi::c_int,
            len: ::core::ffi::c_uint,
            offset: u64,
            flags: ::core::ffi::c_int,
        ) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_sync_file_range(sqe, fd, len, offset, flags) };
        }
    }
}
