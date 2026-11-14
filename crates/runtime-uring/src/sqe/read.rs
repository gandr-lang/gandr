pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        pub unsafe fn prep_read(
            &mut self,
            fd: ::core::ffi::c_int,
            buf: *mut ::core::ffi::c_void,
            nbytes: ::core::ffi::c_uint,
            offset: u64,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_read(sqe, fd, buf, nbytes, offset) };
        }

        pub unsafe fn prep_read_fixed(
            &mut self,
            fd: ::core::ffi::c_int,
            buf: *mut ::core::ffi::c_void,
            nbytes: ::core::ffi::c_uint,
            offset: u64,
            buf_index: ::core::ffi::c_int,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_read_fixed(sqe, fd, buf, nbytes, offset, buf_index)
            };
        }

        pub unsafe fn prep_read_multishot(
            &mut self,
            fd: ::core::ffi::c_int,
            nbytes: ::core::ffi::c_uint,
            offset: u64,
            buf_group: ::core::ffi::c_int,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_read_multishot(sqe, fd, nbytes, offset, buf_group)
            };
        }

        pub unsafe fn prep_readv(
            &mut self,
            fd: ::core::ffi::c_int,
            iovecs: *const ::liburing_rs::iovec,
            nr_vecs: ::core::ffi::c_uint,
            offset: u64,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_readv(sqe, fd, iovecs, nr_vecs, offset) };
        }

        pub unsafe fn prep_readv2(
            &mut self,
            fd: ::core::ffi::c_int,
            iovecs: *const ::liburing_rs::iovec,
            nr_vecs: ::core::ffi::c_uint,
            offset: u64,
            flags: ::core::ffi::c_int,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_readv2(sqe, fd, iovecs, nr_vecs, offset, flags) };
        }

        pub unsafe fn prep_readv_fixed(
            &mut self,
            fd: ::core::ffi::c_int,
            iovecs: *const ::liburing_rs::iovec,
            nr_vecs: ::core::ffi::c_uint,
            offset: u64,
            flags: ::core::ffi::c_int,
            buf_index: ::core::ffi::c_int,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_readv_fixed(
                    sqe, fd, iovecs, nr_vecs, offset, flags, buf_index,
                )
            };
        }
    }
}
