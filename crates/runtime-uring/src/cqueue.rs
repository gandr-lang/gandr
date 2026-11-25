//! The completion queue: it gives the ready completions, or waits for them.

use ::core::marker::PhantomData;
use ::core::ptr::NonNull;

use crate::IoUring;
use crate::arg::Answer;
use crate::arg::Count;
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
    ring: NonNull<::liburing_rs::io_uring>,
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
        let ring = ring.ring();
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
        Count(count): Count<usize>,
    ) -> ::std::io::Result<CqesWait<'_, C>>
    {
        let ring = self.ring;
        let mut cqe_ptr = NonNull::<::liburing_rs::io_uring_cqe>::dangling();

        if count == 0 {
            return Ok(CqesWait::new(ring, cqe_ptr, Count(count)));
        }

        #[expect(
            clippy::as_conversions,
            clippy::cast_possible_truncation,
            reason = "WIP"
        )]
        let wait_nr = count as u32;

        // SAFETY: `ring` is the live ring that this queue borrows, and
        // `cqe_ptr` has room for the pointer that liburing writes.
        Answer(unsafe {
            ::liburing_rs::io_uring_wait_cqe_nr(ring.as_ptr(), (&raw mut cqe_ptr).cast(), wait_nr)
        })
        .sys_zero()?;

        Ok(CqesWait::new(ring, cqe_ptr, Count(count)))
    }
}

#[cfg(test)]
pub mod test
{
    use crate::arg::Count;
    use crate::arg::UserData;
    use crate::cqueue::CompletionQueue;
    use crate::ring::IoUring;

    #[test]
    #[cfg_attr(
        miri,
        ignore = "it sets up a ring through liburing, which Miri cannot run"
    )]
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
            #[cfg_attr(
                miri,
                ignore = "it sets up a ring through liburing, which Miri cannot run"
            )]
            fn zero()
            {
                let mut ring = IoUring::new().unwrap();
                let mut cq = ring.cqueue();

                let cqes = cq.ready().collect::<Vec<_>>();
                assert_eq!(cqes.len(), 0);
            }

            #[test]
            #[cfg_attr(
                miri,
                ignore = "it sets up a ring through liburing, which Miri cannot run"
            )]
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
                let Count(num) = sq.submit_and_wait(Count(num)).unwrap();
                let cqes = cq.ready().collect::<Vec<_>>();
                assert_eq!(cqes.len(), usize::try_from(num).unwrap());
            }

            #[test]
            #[cfg_attr(
                miri,
                ignore = "it sets up a ring through liburing, which Miri cannot run"
            )]
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
                let Count(num) = sq.submit_and_wait(Count(num)).unwrap();
                let cqes = cq.ready().collect::<Vec<_>>();
                assert_eq!(cqes.len(), usize::try_from(num).unwrap());
            }
        }

        mod wait
        {
            use super::*;

            #[test]
            #[cfg_attr(
                miri,
                ignore = "it sets up a ring through liburing, which Miri cannot run"
            )]
            fn zero()
            {
                let mut ring = IoUring::new().unwrap();
                let mut cq = ring.cqueue();

                let count = cq.wait(Count(0)).unwrap().count();
                assert_eq!(count, 0);
            }

            #[test]
            #[cfg_attr(
                miri,
                ignore = "it sets up a ring through liburing, which Miri cannot run"
            )]
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
                let Count(num) = sq.submit_and_wait(Count(num)).unwrap();
                let count = cq.wait(Count(1)).unwrap().count();
                assert_eq!(count, usize::try_from(num).unwrap());
            }

            #[test]
            #[cfg_attr(
                miri,
                ignore = "it sets up a ring through liburing, which Miri cannot run"
            )]
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
                let Count(num) = sq.submit_and_wait(Count(num)).unwrap();
                let count = cq.wait(Count(2)).unwrap().count();
                assert_eq!(count, usize::try_from(num).unwrap());
            }

            /// A wait for two completions on a ring of entries of 32 bytes
            /// gives each completion's own data in order: the run steps one
            /// entry of 32 bytes, never 16.
            #[test]
            #[cfg_attr(
                miri,
                ignore = "it sets up a ring through liburing, which Miri cannot run"
            )]
            fn two_of_32_bytes()
            {
                let mut ring = IoUring::builder().setup_cqe32().build().unwrap();
                let (mut sq, mut cq) = ring.queues();

                for data in [1, 2] {
                    let mut sqe = sq.get_sqe().unwrap();
                    // SAFETY: a no-op reads no pointer and names no
                    // descriptor.
                    unsafe {
                        sqe.prep_nop();
                    }
                    // SAFETY: the data is a plain number, which the kernel
                    // gives back unread.
                    unsafe {
                        sqe.set_data64(UserData(data));
                    }
                }

                let num = sq.submit_and_wait(Count(2)).unwrap();
                assert_eq!(num, Count(2));
                let data = cq
                    .wait(Count(2))
                    .unwrap()
                    .map(|cqe| cqe.cqe().user_data)
                    .collect::<Vec<_>>();
                assert_eq!(data, [1, 2]);
            }
        }
    }
}
