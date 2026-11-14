pub mod repr {
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_> {
        pub unsafe fn prep_waitid(
            &mut self,
            idtype: ::liburing_rs::idtype_t,
            id: ::liburing_rs::id_t,
            infop: *mut ::liburing_rs::siginfo_t,
            options: ::core::ffi::c_int,
            flags: ::core::ffi::c_uint,
        ) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_waitid(sqe, idtype, id, infop, options, flags) };
        }
    }
}
