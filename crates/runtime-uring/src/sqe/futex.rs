pub mod repr {
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_> {
        pub unsafe fn prep_futex_wait(
            &mut self,
            futex: *const u32,
            val: u64,
            mask: u64,
            futex_flags: u32,
            flags: ::core::ffi::c_uint,
        ) {
            let sqe = &raw mut *self.sqe;
            // FIXME: remove if upstream merges const changes
            let futex = futex.cast_mut();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_futex_wait(sqe, futex, val, mask, futex_flags, flags) };
        }

        pub unsafe fn prep_futex_waitv(
            &mut self,
            futex: *const ::liburing_rs::futex_waitv,
            nr_futex: u32,
            flags: ::core::ffi::c_uint,
        ) {
            let sqe = &raw mut *self.sqe;
            // FIXME: remove if upstream merges const changes
            let futex = futex.cast_mut();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_futex_waitv(sqe, futex, nr_futex, flags) };
        }

        pub unsafe fn prep_futex_wake(
            &mut self,
            futex: *const u32,
            val: u64,
            mask: u64,
            futex_flags: u32,
            flags: ::core::ffi::c_uint,
        ) {
            let sqe = &raw mut *self.sqe;
            // FIXME: remove if upstream merges const changes
            let futex = futex.cast_mut();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_futex_wake(sqe, futex, val, mask, futex_flags, flags) };
        }
    }
}
