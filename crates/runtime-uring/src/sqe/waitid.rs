//! The preparers of waits on processes.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::arg::Code;
    use crate::arg::Flags;
    use crate::arg::Id;
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for a wait for a state change of the process `id`
        /// of kind `idtype`, written to `infop`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `infop` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_waitid(
            &mut self,
            Code(idtype): Code<::liburing_rs::idtype_t>,
            Id(id): Id,
            infop: *mut ::liburing_rs::siginfo_t,
            Flags(options): Flags<::core::ffi::c_int>,
            Flags(flags): Flags<::core::ffi::c_uint>,
        )
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_waitid(sqe, idtype, id, infop, options, flags);
            }
        }
    }
}
