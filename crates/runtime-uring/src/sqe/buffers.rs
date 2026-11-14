pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        pub unsafe fn prep_provide_buffers(
            &mut self,
            addr: *mut ::core::ffi::c_void,
            len: ::core::ffi::c_int,
            nr: ::core::ffi::c_int,
            bgid: ::core::ffi::c_int,
            bid: ::core::ffi::c_int,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_provide_buffers(sqe, addr, len, nr, bgid, bid) };
        }

        pub unsafe fn prep_remove_buffers(
            &mut self,
            nr: ::core::ffi::c_int,
            bgid: ::core::ffi::c_int,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_remove_buffers(sqe, nr, bgid) };
        }
    }
}
