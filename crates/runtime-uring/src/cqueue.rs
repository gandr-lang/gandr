use ::core::marker::PhantomData;
use ::core::ptr::NonNull;

use crate::IoUring;
use crate::cqe::CqesReady;
use crate::cqe::CqesWait;
use crate::cqe::kind::Cqe16;
use crate::sqe::kind::Sqe64;
use crate::sys::SysResult as _;

#[non_exhaustive]
pub struct CompletionQueue<'ring, C = Cqe16>
{
    pub(crate) ring: NonNull<::liburing_rs::io_uring>,
    marker: PhantomData<&'ring mut IoUring<'static, Sqe64, C>>,
}
impl<'ring, C> CompletionQueue<'ring, C>
where
    C: crate::cqe::Kind,
{
    pub(crate) fn new<S>(ring: &'ring IoUring<S, C>) -> Self
    {
        let ring = NonNull::from(&ring.ring);
        Self {
            ring,
            marker: PhantomData,
        }
    }

    pub fn ready(&mut self) -> CqesReady<'_, C>
    {
        CqesReady::new(self.ring)
    }

    /// # Errors
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

        // SAFETY:
        unsafe {
            ::liburing_rs::io_uring_wait_cqe_nr(ring.as_ptr(), (&raw mut cqe_ptr).cast(), wait_nr)
        }
        .sys_zero()?;

        Ok(CqesWait::new(ring, cqe_ptr, count))
    }
}

#[cfg(test)]
pub(crate) mod test
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
                unsafe { sqe.prep_nop() };

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
                unsafe { sqe.prep_nop() };

                let mut sqe = sq.get_sqe().unwrap();
                unsafe { sqe.prep_nop() };

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
                unsafe { sqe.prep_nop() };

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
                unsafe { sqe.prep_nop() };

                let mut sqe = sq.get_sqe().unwrap();
                unsafe { sqe.prep_nop() };

                let num = 2;
                let num = sq.submit_and_wait(num).unwrap();
                let count = cq.wait(2).unwrap().count();
                assert_eq!(count, usize::try_from(num).unwrap());
            }
        }
    }
}
