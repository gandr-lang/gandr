pub mod repr {
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_> {
        pub unsafe fn prep_files_update(
            &mut self,
            fds: *const ::core::ffi::c_int,
            nr_fds: ::core::ffi::c_uint,
            offset: ::core::ffi::c_int,
        ) {
            let sqe = &raw mut *self.sqe;
            // FIXME: remove if upstream merges const changes
            let fds = fds.cast_mut();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_files_update(sqe, fds, nr_fds, offset) };
        }
    }
}
