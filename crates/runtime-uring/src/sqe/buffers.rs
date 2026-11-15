//! The preparers of hand-overs and removals of provided buffers.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::arg::Count;
    use crate::arg::Index;
    use crate::arg::Len;
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for a hand-over of `nr` buffers of `len` bytes
        /// each at `addr` to the buffer group `bgid`, with identifiers from
        /// `bid`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `addr` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_provide_buffers(
            &mut self,
            addr: *mut ::core::ffi::c_void,
            Len(len): Len<::core::ffi::c_int>,
            Count(nr): Count<::core::ffi::c_int>,
            Index(bgid): Index<::core::ffi::c_int>,
            Index(bid): Index<::core::ffi::c_int>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_provide_buffers(sqe, addr, len, nr, bgid, bid);
            }
        }

        /// Prepares the entry for a removal of `nr` buffers from the buffer
        /// group `bgid`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: The owner's crate marks each preparer `unsafe`.
        ///   This one reads no pointer and names no descriptor, so it holds no
        ///   invariant of its own.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_remove_buffers(
            &mut self,
            Count(nr): Count<::core::ffi::c_int>,
            Index(bgid): Index<::core::ffi::c_int>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_remove_buffers(sqe, nr, bgid);
            }
        }
    }
}
