//! The preparers of epoll controls and waits.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for the epoll control `op` for `fd` on the epoll
        /// instance `epfd`, with the event at `ev`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `ev` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion.
        ///   `epfd` and `fd` are open descriptors, or slots of the ring's file
        ///   table when the entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_epoll_ctl(
            &mut self,
            epfd: ::core::ffi::c_int,
            fd: ::core::ffi::c_int,
            op: ::core::ffi::c_int,
            ev: *const ::liburing_rs::epoll_event,
        )
        {
            let sqe = &raw mut *self.sqe();
            // liburing's signature takes a mutable pointer here, though the
            // kernel only reads it; the cast leaves when liburing
            // takes a constant pointer.
            let ev = ev.cast_mut();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_epoll_ctl(sqe, epfd, fd, op, ev);
            }
        }

        /// Prepares the entry for a wait for at most `maxevents` events on the
        /// epoll instance `fd`, written to `events`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `events` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion. `fd`
        ///   is an open descriptor, or a slot of the ring's file table when the
        ///   entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_epoll_wait(
            &mut self,
            fd: ::core::ffi::c_int,
            events: *mut ::liburing_rs::epoll_event,
            maxevents: ::core::ffi::c_int,
            flags: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_epoll_wait(sqe, fd, events, maxevents, flags);
            }
        }
    }
}
