pub mod repr {
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_> {
        pub unsafe fn prep_epoll_ctl(
            &mut self,
            epfd: ::core::ffi::c_int,
            fd: ::core::ffi::c_int,
            op: ::core::ffi::c_int,
            ev: *const ::liburing_rs::epoll_event,
        ) {
            let sqe = &raw mut *self.sqe;
            // FIXME: remove if upstream merges const changes
            let ev = ev.cast_mut();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_epoll_ctl(sqe, epfd, fd, op, ev) };
        }

        pub unsafe fn prep_epoll_wait(
            &mut self,
            fd: ::core::ffi::c_int,
            events: *mut ::liburing_rs::epoll_event,
            maxevents: ::core::ffi::c_int,
            flags: ::core::ffi::c_uint,
        ) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_epoll_wait(sqe, fd, events, maxevents, flags) };
        }
    }
}
