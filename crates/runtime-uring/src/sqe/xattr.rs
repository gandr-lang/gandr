//! The preparers of reads and writes of extended attributes.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::arg::Bytes;
    use crate::arg::Fd;
    use crate::arg::Flags;
    use crate::arg::Len;
    use crate::arg::Text;
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for a read of the extended attribute `name` of
        /// `fd`, at most `len` bytes into `value`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `name` and `value` point to memory that stays
        ///   valid, and does not move, until the kernel posts the entry's
        ///   completion. `fd` is an open descriptor, or a slot of the ring's
        ///   file table when the entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_fgetxattr(
            &mut self,
            Fd(fd): Fd,
            Text(name): Text,
            Bytes(value): Bytes<*mut ::core::ffi::c_char>,
            Len(len): Len<::core::ffi::c_uint>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_fgetxattr(sqe, fd, name, value, len);
            }
        }

        /// Prepares the entry for a write of the extended attribute `name` of
        /// `fd` from the `len` bytes at `value`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `name` and `value` point to memory that stays
        ///   valid, and does not move, until the kernel posts the entry's
        ///   completion. `fd` is an open descriptor, or a slot of the ring's
        ///   file table when the entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_fsetxattr(
            &mut self,
            Fd(fd): Fd,
            Text(name): Text,
            Bytes(value): Bytes<*mut ::core::ffi::c_char>,
            Flags(flags): Flags<::core::ffi::c_int>,
            Len(len): Len<::core::ffi::c_uint>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_fsetxattr(sqe, fd, name, value, flags, len);
            }
        }

        /// Prepares the entry for a read of the extended attribute `name` of
        /// `path`, at most `len` bytes into `value`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `name`, `value` and `path` point to memory that
        ///   stays valid, and does not move, until the kernel posts the entry's
        ///   completion.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_getxattr(
            &mut self,
            Text(name): Text,
            Bytes(value): Bytes<*mut ::core::ffi::c_char>,
            Text(path): Text,
            Len(len): Len<::core::ffi::c_uint>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_getxattr(sqe, name, value, path, len);
            }
        }

        /// Prepares the entry for a write of the extended attribute `name` of
        /// `path` from the `len` bytes at `value`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `name`, `value` and `path` point to memory that
        ///   stays valid, and does not move, until the kernel posts the entry's
        ///   completion.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_setxattr(
            &mut self,
            Text(name): Text,
            Bytes(value): Bytes<*const ::core::ffi::c_char>,
            Text(path): Text,
            Flags(flags): Flags<::core::ffi::c_int>,
            Len(len): Len<::core::ffi::c_uint>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_setxattr(sqe, name, value, path, flags, len);
            }
        }
    }
}
