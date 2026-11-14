pub mod repr {
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_> {
        pub unsafe fn prep_madvise(&mut self, addr: *mut ::core::ffi::c_void, length: u32, advice: ::core::ffi::c_int) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_madvise(sqe, addr, length, advice) };
        }

        pub unsafe fn prep_madvise64(
            &mut self,
            addr: *mut ::core::ffi::c_void,
            length: ::liburing_rs::off_t,
            advice: ::core::ffi::c_int,
        ) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_madvise64(sqe, addr, length, advice) };
        }
    }
}
