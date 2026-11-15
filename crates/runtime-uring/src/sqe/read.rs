//! The preparers of reads.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for a read of at most `nbytes` bytes at `offset`
        /// of `fd` into `buf`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `buf` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion. `fd`
        ///   is an open descriptor, or a slot of the ring's file table when the
        ///   entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_read(
            &mut self,
            fd: ::core::ffi::c_int,
            buf: *mut ::core::ffi::c_void,
            nbytes: ::core::ffi::c_uint,
            offset: u64,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_read(sqe, fd, buf, nbytes, offset);
            }
        }

        /// Prepares the entry for a read of at most `nbytes` bytes at `offset`
        /// of `fd` into `buf`, a registered buffer of index `buf_index`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `buf` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion. `fd`
        ///   is an open descriptor, or a slot of the ring's file table when the
        ///   entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_read_fixed(
            &mut self,
            fd: ::core::ffi::c_int,
            buf: *mut ::core::ffi::c_void,
            nbytes: ::core::ffi::c_uint,
            offset: u64,
            buf_index: ::core::ffi::c_int,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_read_fixed(sqe, fd, buf, nbytes, offset, buf_index);
            }
        }

        /// Prepares the entry for a read of `fd` that stays armed and takes
        /// each buffer from the group `buf_group`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `fd` is an open descriptor, or a slot of the
        ///   ring's file table when the entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_read_multishot(
            &mut self,
            fd: ::core::ffi::c_int,
            nbytes: ::core::ffi::c_uint,
            offset: u64,
            buf_group: ::core::ffi::c_int,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_read_multishot(sqe, fd, nbytes, offset, buf_group);
            }
        }

        /// Prepares the entry for a read at `offset` of `fd` into the `nr_vecs`
        /// buffers that `iovecs` lists.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `iovecs` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion. `fd`
        ///   is an open descriptor, or a slot of the ring's file table when the
        ///   entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_readv(
            &mut self,
            fd: ::core::ffi::c_int,
            iovecs: *const ::liburing_rs::iovec,
            nr_vecs: ::core::ffi::c_uint,
            offset: u64,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_readv(sqe, fd, iovecs, nr_vecs, offset);
            }
        }

        /// Prepares the entry for a read at `offset` of `fd` into the `nr_vecs`
        /// buffers that `iovecs` lists, with the flags `flags`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `iovecs` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion. `fd`
        ///   is an open descriptor, or a slot of the ring's file table when the
        ///   entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_readv2(
            &mut self,
            fd: ::core::ffi::c_int,
            iovecs: *const ::liburing_rs::iovec,
            nr_vecs: ::core::ffi::c_uint,
            offset: u64,
            flags: ::core::ffi::c_int,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_readv2(sqe, fd, iovecs, nr_vecs, offset, flags);
            }
        }

        /// Prepares the entry for a read at `offset` of `fd` into the `nr_vecs`
        /// registered buffers that `iovecs` lists, from index `buf_index`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `iovecs` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion. `fd`
        ///   is an open descriptor, or a slot of the ring's file table when the
        ///   entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_readv_fixed(
            &mut self,
            fd: ::core::ffi::c_int,
            iovecs: *const ::liburing_rs::iovec,
            nr_vecs: ::core::ffi::c_uint,
            offset: u64,
            flags: ::core::ffi::c_int,
            buf_index: ::core::ffi::c_int,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_readv_fixed(
                    sqe, fd, iovecs, nr_vecs, offset, flags, buf_index,
                );
            }
        }
    }
}
