//! The preparers of hard links and the timeouts of linked entries.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for a hard link at `newpath` to `oldpath`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `oldpath` and `newpath` point to memory that
        ///   stays valid, and does not move, until the kernel posts the entry's
        ///   completion.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_link(
            &mut self,
            oldpath: *const ::core::ffi::c_char,
            newpath: *const ::core::ffi::c_char,
            flags: ::core::ffi::c_int,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_link(sqe, oldpath, newpath, flags);
            }
        }

        /// Prepares the entry for a timeout of `ts` for the entry that comes
        /// before this one in its link.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `ts` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_link_timeout(
            &mut self,
            ts: *const ::liburing_rs::__kernel_timespec,
            flags: ::core::ffi::c_uint,
        )
        {
            let sqe = &raw mut *self.sqe;
            // liburing's signature takes a mutable pointer here, though the
            // kernel only reads it; the cast leaves when liburing
            // takes a constant pointer.
            let ts = ts.cast_mut();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_link_timeout(sqe, ts, flags);
            }
        }

        /// Prepares the entry for a hard link at `newpath` under `newdfd` to
        /// `oldpath` under `olddfd`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `oldpath` and `newpath` point to memory that
        ///   stays valid, and does not move, until the kernel posts the entry's
        ///   completion. `olddfd` and `newdfd` are open descriptors, or slots
        ///   of the ring's file table when the entry carries the fixed-file
        ///   flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_linkat(
            &mut self,
            olddfd: ::core::ffi::c_int,
            oldpath: *const ::core::ffi::c_char,
            newdfd: ::core::ffi::c_int,
            newpath: *const ::core::ffi::c_char,
            flags: ::core::ffi::c_int,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_linkat(sqe, olddfd, oldpath, newdfd, newpath, flags);
            }
        }
    }
}
