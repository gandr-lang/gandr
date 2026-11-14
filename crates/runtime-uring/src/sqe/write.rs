pub mod repr {
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_> {
        pub unsafe fn prep_write(
            &mut self,
            fd: ::core::ffi::c_int,
            buf: *const ::core::ffi::c_void,
            nbytes: ::core::ffi::c_uint,
            offset: u64,
        ) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_write(sqe, fd, buf, nbytes, offset) };
        }

        pub unsafe fn prep_write_fixed(
            &mut self,
            fd: ::core::ffi::c_int,
            buf: *const ::core::ffi::c_void,
            nbytes: ::core::ffi::c_uint,
            offset: u64,
            buf_index: ::core::ffi::c_int,
        ) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_write_fixed(sqe, fd, buf, nbytes, offset, buf_index) };
        }

        pub unsafe fn prep_writev(
            &mut self,
            fd: ::core::ffi::c_int,
            iovecs: *const ::liburing_rs::iovec,
            nr_vecs: ::core::ffi::c_uint,
            offset: u64,
        ) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_writev(sqe, fd, iovecs, nr_vecs, offset) };
        }

        pub unsafe fn prep_writev2(
            &mut self,
            fd: ::core::ffi::c_int,
            iovecs: *const ::liburing_rs::iovec,
            nr_vecs: ::core::ffi::c_uint,
            offset: u64,
            flags: ::core::ffi::c_int,
        ) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_writev2(sqe, fd, iovecs, nr_vecs, offset, flags) };
        }

        pub unsafe fn prep_writev_fixed(
            &mut self,
            fd: ::core::ffi::c_int,
            iovecs: *const ::liburing_rs::iovec,
            nr_vecs: ::core::ffi::c_uint,
            offset: u64,
            flags: ::core::ffi::c_int,
            buf_index: ::core::ffi::c_int,
        ) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_writev_fixed(sqe, fd, iovecs, nr_vecs, offset, flags, buf_index) };
        }
    }
}
