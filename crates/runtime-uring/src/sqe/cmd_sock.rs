pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        #[inline]
        pub unsafe fn prep_cmd_sock(
            &mut self,
            cmd_op: ::core::ffi::c_int,
            fd: ::core::ffi::c_int,
            level: ::core::ffi::c_int,
            optname: ::core::ffi::c_int,
            optval: *mut ::core::ffi::c_void,
            optlen: ::core::ffi::c_int,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_cmd_sock(
                    sqe, cmd_op, fd, level, optname, optval, optlen,
                );
            }
        }
    }
}
