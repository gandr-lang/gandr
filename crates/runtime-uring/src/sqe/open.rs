//! The preparers of opens of files.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::arg::Fd;
    use crate::arg::Flags;
    use crate::arg::Index;
    use crate::arg::Mode;
    use crate::arg::Text;
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for an open of `path` with the flags `flags` and
        /// the mode `mode`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `path` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_open(
            &mut self,
            Text(path): Text,
            Flags(flags): Flags<::core::ffi::c_int>,
            Mode(mode): Mode<::liburing_rs::mode_t>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_open(sqe, path, flags, mode);
            }
        }

        /// Prepares the entry for an open of `path` into the slot `file_index`
        /// of the ring's file table.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `path` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_open_direct(
            &mut self,
            Text(path): Text,
            Flags(flags): Flags<::core::ffi::c_int>,
            Mode(mode): Mode<::liburing_rs::mode_t>,
            Index(file_index): Index<::core::ffi::c_uint>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_open_direct(sqe, path, flags, mode, file_index);
            }
        }

        /// Prepares the entry for an open of `path` under `dfd` with the flags
        /// `flags` and the mode `mode`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `path` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion.
        ///   `dfd` is an open descriptor, or a slot of the ring's file table
        ///   when the entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_openat(
            &mut self,
            Fd(dfd): Fd,
            Text(path): Text,
            Flags(flags): Flags<::core::ffi::c_int>,
            Mode(mode): Mode<::liburing_rs::mode_t>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_openat(sqe, dfd, path, flags, mode);
            }
        }

        /// Prepares the entry for an open of `path` under `dfd` as `how` says.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `path` and `how` point to memory that stays
        ///   valid, and does not move, until the kernel posts the entry's
        ///   completion. `dfd` is an open descriptor, or a slot of the ring's
        ///   file table when the entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_openat2(
            &mut self,
            Fd(dfd): Fd,
            Text(path): Text,
            how: *const ::liburing_rs::open_how,
        )
        {
            let sqe = &raw mut *self.sqe();
            // liburing's signature takes a mutable pointer here, though the
            // kernel only reads it; the cast leaves when liburing
            // takes a constant pointer.
            let how = how.cast_mut();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_openat2(sqe, dfd, path, how);
            }
        }

        /// Prepares the entry for an open of `path` under `dfd` as `how` says,
        /// into the slot `file_index` of the ring's file table.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `path` and `how` point to memory that stays
        ///   valid, and does not move, until the kernel posts the entry's
        ///   completion. `dfd` is an open descriptor, or a slot of the ring's
        ///   file table when the entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_openat2_direct(
            &mut self,
            Fd(dfd): Fd,
            Text(path): Text,
            how: *const ::liburing_rs::open_how,
            Index(file_index): Index<::core::ffi::c_uint>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // liburing's signature takes a mutable pointer here, though the
            // kernel only reads it; the cast leaves when liburing
            // takes a constant pointer.
            let how = how.cast_mut();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_openat2_direct(sqe, dfd, path, how, file_index);
            }
        }

        /// Prepares the entry for an open of `path` under `dfd` into the slot
        /// `file_index` of the ring's file table.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `path` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion.
        ///   `dfd` is an open descriptor, or a slot of the ring's file table
        ///   when the entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_openat_direct(
            &mut self,
            Fd(dfd): Fd,
            Text(path): Text,
            Flags(flags): Flags<::core::ffi::c_int>,
            Mode(mode): Mode<::liburing_rs::mode_t>,
            Index(file_index): Index<::core::ffi::c_uint>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_openat_direct(sqe, dfd, path, flags, mode, file_index);
            }
        }
    }
}
