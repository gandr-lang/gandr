//! The completion queue: it gives the ready completions, or waits for them.

use ::core::marker::PhantomData;
use ::core::ptr::NonNull;

use crate::IoUring;
use crate::cqe::CqesReady;
use crate::cqe::CqesWait;
use crate::cqe::kind::Cqe16;
use crate::sqe::kind::Sqe64;
use crate::sys::SysResult as _;

/// A borrow of the ring's completion queue.
#[non_exhaustive]
pub struct CompletionQueue<'ring, C = Cqe16>
{
    /// The ring that liburing holds.
    pub(crate) ring: NonNull<::liburing_rs::io_uring>,
    /// The borrow of the ring.
    marker: PhantomData<&'ring mut IoUring<'static, Sqe64, C>>,
}
impl<'ring, C> CompletionQueue<'ring, C>
where
    C: crate::cqe::Kind,
{
    /// The completion queue of `ring`.
    ///
    /// # Specification
    ///
    /// trivial.
    pub(crate) fn new<S>(ring: &'ring IoUring<'_, S, C>) -> Self
    {
        let ring = NonNull::from(&ring.ring);
        Self {
            ring,
            marker: PhantomData,
        }
    }

    /// The completions that are ready now.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    pub fn ready(&mut self) -> CqesReady<'_, C>
    {
        CqesReady::new(self.ring)
    }

    /// Waits until `count` completions are ready, and gives them.
    ///
    /// # Errors
    ///
    /// The kernel refuses the wait and gives its error number.
    ///
    /// # Specification
    ///
    /// - fails: the kernel refuses the wait.
    /// - executable: none — the outcome is the kernel's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a wait for zero, one or two completions gives as many
    ///   as the submissions before it.
    /// - witness: `cqueue::test::cqes::wait::zero`
    /// - witness: `cqueue::test::cqes::wait::one`
    /// - witness: `cqueue::test::cqes::wait::two`
    #[inline]
    pub fn wait(
        &mut self,
        count: usize,
    ) -> ::std::io::Result<CqesWait<'_, C>>
    {
        let ring = self.ring;
        let mut cqe_ptr = NonNull::<::liburing_rs::io_uring_cqe>::dangling();

        if count == 0 {
            return Ok(CqesWait::new(ring, cqe_ptr, count));
        }

        #[expect(
            clippy::as_conversions,
            clippy::cast_possible_truncation,
            reason = "WIP"
        )]
        let wait_nr = count as u32;

        // SAFETY: `ring` is the live ring that this queue borrows, and
        // `cqe_ptr` has room for the pointer that liburing writes.
        unsafe {
            ::liburing_rs::io_uring_wait_cqe_nr(ring.as_ptr(), (&raw mut cqe_ptr).cast(), wait_nr)
        }
        .sys_zero()?;

        Ok(CqesWait::new(ring, cqe_ptr, count))
    }
}

#[cfg(test)]
pub mod test
{
    use crate::cqueue::CompletionQueue;
    use crate::ring::IoUring;

    #[test]
    fn new()
    {
        let ring = IoUring::new().unwrap();
        CompletionQueue::new(&ring);
    }

    mod cqes
    {
        use super::*;

        mod ready
        {
            use super::*;

            #[test]
            fn zero()
            {
                let mut ring = IoUring::new().unwrap();
                let mut cq = ring.cqueue();

                let cqes = cq.ready().collect::<Vec<_>>();
                assert_eq!(cqes.len(), 0);
            }

            #[test]
            fn one()
            {
                let mut ring = IoUring::new().unwrap();
                let (mut sq, mut cq) = ring.queues();

                let mut sqe = sq.get_sqe().unwrap();
                // SAFETY: a no-op reads no pointer and names no descriptor.
                unsafe {
                    sqe.prep_nop();
                }

                let num = 1;
                let num = sq.submit_and_wait(num).unwrap();
                let cqes = cq.ready().collect::<Vec<_>>();
                assert_eq!(cqes.len(), usize::try_from(num).unwrap());
            }

            #[test]
            fn two()
            {
                let mut ring = IoUring::new().unwrap();
                let (mut sq, mut cq) = ring.queues();

                let mut sqe = sq.get_sqe().unwrap();
                // SAFETY: a no-op reads no pointer and names no descriptor.
                unsafe {
                    sqe.prep_nop();
                }

                let mut sqe = sq.get_sqe().unwrap();
                // SAFETY: a no-op reads no pointer and names no descriptor.
                unsafe {
                    sqe.prep_nop();
                }

                let num = 2;
                let num = sq.submit_and_wait(num).unwrap();
                let cqes = cq.ready().collect::<Vec<_>>();
                assert_eq!(cqes.len(), usize::try_from(num).unwrap());
            }
        }

        mod wait
        {
            use super::*;

            #[test]
            fn zero()
            {
                let mut ring = IoUring::new().unwrap();
                let mut cq = ring.cqueue();

                let count = cq.wait(0).unwrap().count();
                assert_eq!(count, 0);
            }

            #[test]
            fn one()
            {
                let mut ring = IoUring::new().unwrap();
                let (mut sq, mut cq) = ring.queues();

                let mut sqe = sq.get_sqe().unwrap();
                // SAFETY: a no-op reads no pointer and names no descriptor.
                unsafe {
                    sqe.prep_nop();
                }

                let num = 1;
                let num = sq.submit_and_wait(num).unwrap();
                let count = cq.wait(1).unwrap().count();
                assert_eq!(count, usize::try_from(num).unwrap());
            }

            #[test]
            fn two()
            {
                let mut ring = IoUring::new().unwrap();
                let (mut sq, mut cq) = ring.queues();

                let mut sqe = sq.get_sqe().unwrap();
                // SAFETY: a no-op reads no pointer and names no descriptor.
                unsafe {
                    sqe.prep_nop();
                }

                let mut sqe = sq.get_sqe().unwrap();
                // SAFETY: a no-op reads no pointer and names no descriptor.
                unsafe {
                    sqe.prep_nop();
                }

                let num = 2;
                let num = sq.submit_and_wait(num).unwrap();
                let count = cq.wait(2).unwrap().count();
                assert_eq!(count, usize::try_from(num).unwrap());
            }
        }
    }
}
