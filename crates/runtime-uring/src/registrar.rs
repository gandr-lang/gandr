//! The registrar: it registers files in the ring's file table.

use ::core::marker::PhantomData;
use ::core::ptr::NonNull;
use ::std::os::fd::BorrowedFd;

use crate::IoUring;
use crate::arg::Answer;
use crate::arg::Count;
use crate::sys::SysResult as _;

/// A borrow of the ring that registers files in its file table.
#[non_exhaustive]
pub struct Registrar<'ring>
{
    /// The ring that liburing holds.
    ring: NonNull<::liburing_rs::io_uring>,
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
        let ring = ring.ring();
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
    ///
    /// # Cost
    /// - allocation: the boxed error of a count past 32 bits, error path
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a table of open files holds each file in its slot,
    ///   and a read through a slot gives that file's bytes.
    /// - witness: `registrar::test::register_files`
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
        Answer(unsafe { ::liburing_rs::io_uring_register_files(ring, files, nr_files) })
            .sys_zero()?;
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
    ///
    /// # Cost
    /// - allocation: the boxed error of a count past 32 bits, error path
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a sparse table of slots takes a direct socket in its
    ///   slot.
    /// - witness: `sqe::socket::test::socket_direct`
    /// - witness: `sqe::socket::test::socket_direct_cqe_skip`
    #[inline]
    pub fn register_files_sparse(
        &self,
        Count(nr_files): Count<usize>,
    ) -> ::std::io::Result<()>
    {
        let ring = self.ring.as_ptr();
        let nr_files = u32::try_from(nr_files).map_err(::std::io::Error::other)?;
        // SAFETY: `ring` is the live ring that this registrar borrows.
        Answer(unsafe { ::liburing_rs::io_uring_register_files_sparse(ring, nr_files) })
            .sys_zero()?;
        Ok(())
    }
}

#[cfg(test)]
pub mod test
{
    use ::std::os::fd::AsFd as _;

    use crate::IoUring;
    use crate::arg::Answer;
    use crate::arg::Count;
    use crate::arg::Fd;
    use crate::arg::Flags;
    use crate::arg::Len;
    use crate::arg::Offset;
    use crate::sys::SysResult as _;

    /// A table of two open files holds each in its slot: a read through
    /// slot 1 with the fixed-file flag gives the second file's bytes.
    #[test]
    #[cfg_attr(
        miri,
        ignore = "it sets up a ring through liburing, which Miri cannot run"
    )]
    fn register_files()
    {
        let temp = ::assert_fs::TempDir::new().unwrap();
        let first = temp.path().join("first");
        let second = temp.path().join("second");
        ::std::fs::write(&first, b"first").unwrap();
        ::std::fs::write(&second, b"second").unwrap();
        let first = ::std::fs::File::open(first).unwrap();
        let second = ::std::fs::File::open(second).unwrap();
        let table = [first.as_fd(), second.as_fd()];

        let mut ring = IoUring::new().unwrap();
        ring.registrar().register_files(&table).unwrap();

        let (mut sq, mut cq) = ring.queues();
        let mut buf = [0_u8; 16];
        let mut sqe = sq.get_sqe().unwrap();
        // SAFETY: `buf` stays valid and in place until the wait below gives
        // the completion, and slot 1 of the table holds an open file.
        unsafe {
            sqe.prep_read(Fd(1), (&raw mut buf).cast(), Len(16), Offset(0));
        }
        // SAFETY: the entry names slot 1 of the ring's file table.
        unsafe {
            sqe.set_flags(Flags(::liburing_rs::IOSQE_FIXED_FILE));
        }

        sq.submit_and_wait(Count(1)).unwrap();
        let read = cq
            .wait(Count(1))
            .unwrap()
            .map(|cqe| Answer(cqe.cqe().res).sys_uint().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(read, [Answer(6)]);
        assert_eq!(buf.get(.. 6), Some(&b"second"[..]));
    }
}
