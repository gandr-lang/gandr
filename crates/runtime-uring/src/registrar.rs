use ::core::marker::PhantomData;
use ::core::ptr::NonNull;
use ::std::os::fd::BorrowedFd;

use crate::IoUring;
use crate::sys::SysResult as _;

#[non_exhaustive]
pub struct Registrar<'ring>
{
    pub(crate) ring: NonNull<::liburing_rs::io_uring>,
    marker: PhantomData<&'ring mut IoUring<'static>>,
}

impl<'ring> Registrar<'ring>
{
    pub(crate) fn new<S, C>(ring: &'ring IoUring<S, C>) -> Self
    {
        let ring = NonNull::from(&ring.ring);
        Self {
            ring,
            marker: PhantomData,
        }
    }

    /// # Errors
    pub fn register_files(
        &self,
        files: &'ring [BorrowedFd<'ring>],
    ) -> ::std::io::Result<()>
    {
        let ring = self.ring.as_ptr();
        let nr_files = u32::try_from(files.len()).map_err(::std::io::Error::other)?;
        let files = files.as_ptr().cast();
        // SAFETY:
        unsafe { ::liburing_rs::io_uring_register_files(ring, files, nr_files) }.sys_zero()?;
        Ok(())
    }

    /// # Errors
    pub fn register_files_sparse(
        &self,
        nr_files: usize,
    ) -> ::std::io::Result<()>
    {
        let ring = self.ring.as_ptr();
        let nr_files = u32::try_from(nr_files).map_err(::std::io::Error::other)?;
        // SAFETY:
        unsafe { ::liburing_rs::io_uring_register_files_sparse(ring, nr_files) }.sys_zero()?;
        Ok(())
    }
}
