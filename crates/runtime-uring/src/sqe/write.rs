//! The preparers of writes.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for a write of `nbytes` bytes at `buf` to `fd` at
        /// `offset`.
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
        pub unsafe fn prep_write(
            &mut self,
            fd: ::core::ffi::c_int,
            buf: *const ::core::ffi::c_void,
            nbytes: ::core::ffi::c_uint,
            offset: u64,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_write(sqe, fd, buf, nbytes, offset);
            }
        }

        /// Prepares the entry for a write of `nbytes` bytes at `buf`, a
        /// registered buffer of index `buf_index`, to `fd` at `offset`.
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
        pub unsafe fn prep_write_fixed(
            &mut self,
            fd: ::core::ffi::c_int,
            buf: *const ::core::ffi::c_void,
            nbytes: ::core::ffi::c_uint,
            offset: u64,
            buf_index: ::core::ffi::c_int,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_write_fixed(sqe, fd, buf, nbytes, offset, buf_index);
            }
        }

        /// Prepares the entry for a write to `fd` at `offset` of the `nr_vecs`
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
        pub unsafe fn prep_writev(
            &mut self,
            fd: ::core::ffi::c_int,
            iovecs: *const ::liburing_rs::iovec,
            nr_vecs: ::core::ffi::c_uint,
            offset: u64,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_writev(sqe, fd, iovecs, nr_vecs, offset);
            }
        }

        /// Prepares the entry for a write to `fd` at `offset` of the `nr_vecs`
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
        pub unsafe fn prep_writev2(
            &mut self,
            fd: ::core::ffi::c_int,
            iovecs: *const ::liburing_rs::iovec,
            nr_vecs: ::core::ffi::c_uint,
            offset: u64,
            flags: ::core::ffi::c_int,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_writev2(sqe, fd, iovecs, nr_vecs, offset, flags);
            }
        }

        /// Prepares the entry for a write to `fd` at `offset` of the `nr_vecs`
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
        pub unsafe fn prep_writev_fixed(
            &mut self,
            fd: ::core::ffi::c_int,
            iovecs: *const ::liburing_rs::iovec,
            nr_vecs: ::core::ffi::c_uint,
            offset: u64,
            flags: ::core::ffi::c_int,
            buf_index: ::core::ffi::c_int,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_writev_fixed(
                    sqe, fd, iovecs, nr_vecs, offset, flags, buf_index,
                );
            }
        }
    }
}
