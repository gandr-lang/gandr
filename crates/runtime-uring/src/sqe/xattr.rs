pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        pub unsafe fn prep_fgetxattr(
            &mut self,
            fd: ::core::ffi::c_int,
            name: *const ::core::ffi::c_char,
            value: *mut ::core::ffi::c_char,
            len: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_fgetxattr(sqe, fd, name, value, len) };
        }

        pub unsafe fn prep_fsetxattr(
            &mut self,
            fd: ::core::ffi::c_int,
            name: *const ::core::ffi::c_char,
            value: *mut ::core::ffi::c_char,
            flags: ::core::ffi::c_int,
            len: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_fsetxattr(sqe, fd, name, value, flags, len) };
        }

        pub unsafe fn prep_getxattr(
            &mut self,
            name: *const ::core::ffi::c_char,
            value: *mut ::core::ffi::c_char,
            path: *const ::core::ffi::c_char,
            len: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_getxattr(sqe, name, value, path, len) };
        }

        pub unsafe fn prep_setxattr(
            &mut self,
            name: *const ::core::ffi::c_char,
            value: *const ::core::ffi::c_char,
            path: *const ::core::ffi::c_char,
            flags: ::core::ffi::c_int,
            len: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_setxattr(sqe, name, value, path, flags, len) };
        }
    }
}
