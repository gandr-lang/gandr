//! The registrar: it registers files in the ring's file table.

use ::core::marker::PhantomData;
use ::core::ptr::NonNull;
use ::std::os::fd::BorrowedFd;

use crate::IoUring;
use crate::sys::SysResult as _;

/// A borrow of the ring that registers files in its file table.
#[non_exhaustive]
pub struct Registrar<'ring>
{
    /// The ring that liburing holds.
    pub(crate) ring: NonNull<::liburing_rs::io_uring>,
    /// The borrow of the ring.
    marker: PhantomData<&'ring mut IoUring<'static>>,
}

impl<'ring> Registrar<'ring>
{
    /// The registrar of `ring`.
    ///
    /// # Specification
    ///
    /// trivial.
    pub(crate) fn new<S, C>(ring: &'ring IoUring<'_, S, C>) -> Self
    {
        let ring = NonNull::from(&ring.ring);
        Self {
            ring,
            marker: PhantomData,
        }
    }

    /// Registers `files` as the ring's file table, slot by slot.
    ///
    /// # Errors
    ///
    /// The count of `files` does not fit in 32 bits, or the kernel refuses
    /// the registration and gives its error number.
    ///
    /// # Specification
    ///
    /// - fails: the count does not fit, or the kernel refuses the table.
    /// - executable: none — the outcome is the kernel's.
    #[inline]
    pub fn register_files(
        &self,
        files: &'ring [BorrowedFd<'ring>],
    ) -> ::std::io::Result<()>
    {
        let ring = self.ring.as_ptr();
        let nr_files = u32::try_from(files.len()).map_err(::std::io::Error::other)?;
        let files = files.as_ptr().cast();
        // SAFETY: `ring` is the live ring that this registrar borrows, and
        // `files` stays borrowed for the registrar's life.
        unsafe { ::liburing_rs::io_uring_register_files(ring, files, nr_files) }.sys_zero()?;
        Ok(())
    }

    /// Registers a file table of `nr_files` empty slots.
    ///
    /// # Errors
    ///
    /// `nr_files` does not fit in 32 bits, or the kernel refuses the
    /// registration and gives its error number.
    ///
    /// # Specification
    ///
    /// - fails: the count does not fit, or the kernel refuses the table.
    /// - executable: none — the outcome is the kernel's.
    #[inline]
    pub fn register_files_sparse(
        &self,
        nr_files: usize,
    ) -> ::std::io::Result<()>
    {
        let ring = self.ring.as_ptr();
        let nr_files = u32::try_from(nr_files).map_err(::std::io::Error::other)?;
        // SAFETY: `ring` is the live ring that this registrar borrows.
        unsafe { ::liburing_rs::io_uring_register_files_sparse(ring, nr_files) }.sys_zero()?;
        Ok(())
    }
}
