//! The submission queue: it gives entries to prepare and submits them.

use ::core::marker::PhantomData;
use ::core::ptr::NonNull;

use crate::IoUring;
use crate::arg::Answer;
use crate::arg::Count;
use crate::sqe::Sqes;
use crate::sys::SysResult as _;

/// A borrow of the ring's submission queue.
#[non_exhaustive]
pub struct SubmissionQueue<'ring, S>
{
    /// The ring that liburing holds.
    ring: NonNull<::liburing_rs::io_uring>,
    /// The borrow of the ring.
    marker: PhantomData<&'ring mut IoUring<'static, S, crate::cqe::kind::Cqe16>>,
}

impl<S> SubmissionQueue<'_, S>
{
    /// The ring that liburing holds, for a run of free entries.
    ///
    /// # Specification
    ///
    /// trivial.
    pub(crate) const fn ring(&self) -> NonNull<::liburing_rs::io_uring>
    {
        self.ring
    }
}

impl<'ring, S> SubmissionQueue<'ring, S>
where
    S: crate::sqe::Kind,
{
    /// The submission queue of `ring`.
    ///
    /// # Specification
    ///
    /// trivial.
    pub(crate) fn new<C>(ring: &'ring IoUring<'_, S, C>) -> Self
    {
        let ring = ring.ring();
        Self {
            ring,
            marker: PhantomData,
        }
    }

    /// The next free entry, or nothing when the queue is full.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    pub fn get_sqe(&mut self) -> Option<crate::sqe::repr::Sqe<'_>>
    {
        // SAFETY: `ring` is the live ring that this queue borrows, and the
        // entry's borrow ends with the borrow of `self`.
        unsafe { crate::sqe::get_sqe_raw::<S>(self.ring) }.map(Into::into)
    }

    /// `len` free entries in a row, or nothing when the queue has fewer.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    pub fn get_sqes(
        &mut self,
        Count(len): Count<u32>,
    ) -> Option<Sqes<'_, S>>
    {
        let ring = self.ring.as_ptr();
        // SAFETY: `ring` is the live ring that this queue borrows.
        let rem = unsafe { ::liburing_rs::io_uring_sq_space_left(ring) };
        if rem < len {
            return None;
        }
        Some(Sqes::new(self, Count(len)))
    }

    /// Submits the prepared entries, and gives how many the kernel takes.
    ///
    /// # Errors
    ///
    /// The kernel refuses the submission and gives its error number.
    ///
    /// # Specification
    ///
    /// - fails: the kernel refuses the submission.
    /// - executable: none — the outcome is the kernel's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the kernel takes each prepared entry, and the count
    ///   says how many.
    /// - witness: `sqe::bind::test::bind`
    /// - witness: `sqe::listen::test::listen`
    #[inline]
    pub fn submit(&mut self) -> ::std::io::Result<Count<u32>>
    {
        let ring = self.ring.as_ptr();
        // SAFETY: `ring` is the live ring that this queue borrows.
        let code = unsafe { ::liburing_rs::io_uring_submit(ring) };
        Answer(code).sys_uint().map(|Answer(n)| Count(n))
    }

    /// Submits the prepared entries and waits for `wait_nr` completions, and
    /// gives how many entries the kernel takes.
    ///
    /// # Errors
    ///
    /// The kernel refuses the submission or the wait and gives its error
    /// number.
    ///
    /// # Specification
    ///
    /// - fails: the kernel refuses the submission or the wait.
    /// - executable: none — the outcome is the kernel's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one prepared entry is taken, and its completion is
    ///   ready when the call returns.
    /// - witness: `squeue::test::sqe64::submit_and_wait`
    #[inline]
    pub fn submit_and_wait(
        &mut self,
        Count(wait_nr): Count<u32>,
    ) -> ::std::io::Result<Count<u32>>
    {
        let ring = self.ring.as_ptr();
        // SAFETY: `ring` is the live ring that this queue borrows.
        let code = unsafe { ::liburing_rs::io_uring_submit_and_wait(ring, wait_nr) };
        Answer(code).sys_uint().map(|Answer(n)| Count(n))
    }
}

impl SubmissionQueue<'_, crate::sqe::kind::Sqe128>
{
    /// The next free entry of 128 bytes, or nothing when the queue is full.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    pub fn get_sqe128(&mut self) -> Option<crate::sqe::repr::Sqe128<'_>>
    {
        // SAFETY: `ring` is the live ring that this queue borrows, set up
        // with entries of 128 bytes, and the entry's borrow ends with the
        // borrow of `self`.
        unsafe { crate::sqe::get_sqe_raw::<crate::sqe::kind::Sqe128>(self.ring) }
    }
}

#[cfg(test)]
pub mod test
{
    use crate::IoUringBuilder;
    use crate::arg::Count;
    use crate::ring::IoUring;
    use crate::squeue::SubmissionQueue;

    mod fixture
    {
        use super::*;

        pub mod get_sqe
        {

            use super::*;

            /// A check of the submission queue of a ring that `builder` sets
            /// up, for the case where it gives no entry.
            ///
            /// # Specification
            ///
            /// trivial.
            #[should_panic(expected = r#"called `Option::unwrap()` on a `None` value"#)]
            pub fn none<S, C, State>(builder: IoUringBuilder<'_, S, C, State>)
            where
                S: crate::sqe::Kind,
                C: crate::cqe::Kind,
                State: crate::ring::io_uring_builder::IsComplete,
                State::Entries: crate::ring::io_uring_builder::IsUnset,
            {
                let mut ring = builder.entries(Count(1)).build().unwrap();
                let mut squeue = ring.squeue();
                squeue.get_sqe().unwrap();
                squeue.get_sqe().unwrap();
            }

            /// A check of the submission queue of a ring that `builder` sets
            /// up, for the case where it gives an entry.
            ///
            /// # Specification
            ///
            /// trivial.
            pub fn some<S, C, State>(builder: IoUringBuilder<'_, S, C, State>)
            where
                S: crate::sqe::Kind,
                C: crate::cqe::Kind,
                State: crate::ring::io_uring_builder::IsComplete,
                State::Entries: crate::ring::io_uring_builder::IsUnset,
            {
                let mut ring = builder.entries(Count(1)).build().unwrap();
                let mut squeue = ring.squeue();
                squeue.get_sqe().unwrap();
            }
        }

        pub mod get_sqes
        {
            use super::*;

            /// A check of the submission queue of a ring that `builder` sets
            /// up, for the case where it gives no entry.
            ///
            /// # Specification
            ///
            /// trivial.
            #[should_panic(expected = r#"called `Option::unwrap()` on a `None` value"#)]
            pub fn none<S, C, State>(builder: IoUringBuilder<'_, S, C, State>)
            where
                S: crate::sqe::Kind,
                C: crate::cqe::Kind,
                State: crate::ring::io_uring_builder::IsComplete,
                State::Entries: crate::ring::io_uring_builder::IsUnset,
            {
                let mut ring = builder.entries(Count(1)).build().unwrap();
                let mut squeue = ring.squeue();
                let len = 2u32;
                squeue.get_sqes(Count(len)).unwrap();
            }

            /// A check of the submission queue of a ring that `builder` sets
            /// up, for a run of one entry.
            ///
            /// # Specification
            ///
            /// trivial.
            pub fn some_one<S, C, State>(builder: IoUringBuilder<'_, S, C, State>)
            where
                S: crate::sqe::Kind,
                C: crate::cqe::Kind,
                State: crate::ring::io_uring_builder::IsComplete,
                State::Entries: crate::ring::io_uring_builder::IsUnset,
            {
                let mut ring = builder.entries(Count(1)).build().unwrap();
                let mut squeue = ring.squeue();
                let len = 1u32;
                let num = squeue.get_sqes(Count(len)).unwrap().count();
                assert_eq!(num, usize::try_from(len).unwrap());
            }

            /// A check of the submission queue of a ring that `builder` sets
            /// up, for a run of many entries.
            ///
            /// # Specification
            ///
            /// trivial.
            pub fn some_many<S, C, State>(builder: IoUringBuilder<'_, S, C, State>)
            where
                S: crate::sqe::Kind,
                C: crate::cqe::Kind,
                State: crate::ring::io_uring_builder::IsComplete,
                State::Entries: crate::ring::io_uring_builder::IsUnset,
            {
                let mut ring = builder.entries(Count(1024)).build().unwrap();
                let mut squeue = ring.squeue();
                let len = 256u32;
                let num = squeue.get_sqes(Count(len)).unwrap().count();
                assert_eq!(num, usize::try_from(len).unwrap());
            }
        }
    }

    mod sqe64
    {
        use super::*;

        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring through liburing, which Miri cannot run"
        )]
        fn new()
        {
            let ring = IoUring::new().unwrap();
            SubmissionQueue::new(&ring);
        }

        mod get_sqe
        {
            use super::*;

            #[test]
            #[cfg_attr(
                miri,
                ignore = "it sets up a ring through liburing, which Miri cannot run"
            )]
            #[should_panic(expected = r#"called `Option::unwrap()` on a `None` value"#)]
            fn none()
            {
                let builder = IoUring::builder();
                self::fixture::get_sqe::none(builder);
            }

            #[test]
            #[cfg_attr(
                miri,
                ignore = "it sets up a ring through liburing, which Miri cannot run"
            )]
            fn some()
            {
                let builder = IoUring::builder();
                self::fixture::get_sqe::some(builder);
            }
        }

        mod get_sqes
        {
            use super::*;

            #[test]
            #[cfg_attr(
                miri,
                ignore = "it sets up a ring through liburing, which Miri cannot run"
            )]
            #[should_panic(expected = r#"called `Option::unwrap()` on a `None` value"#)]
            fn none()
            {
                let builder = IoUring::builder();
                self::fixture::get_sqes::none(builder);
            }

            #[test]
            #[cfg_attr(
                miri,
                ignore = "it sets up a ring through liburing, which Miri cannot run"
            )]
            fn some_one()
            {
                let builder = IoUring::builder();
                self::fixture::get_sqes::some_one(builder);
            }

            #[test]
            #[cfg_attr(
                miri,
                ignore = "it sets up a ring through liburing, which Miri cannot run"
            )]
            fn some_many()
            {
                let builder = IoUring::builder();
                self::fixture::get_sqes::some_many(builder);
            }
        }

        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring through liburing, which Miri cannot run"
        )]
        fn submit_and_wait()
        {
            let mut ring = IoUring::new().unwrap();
            let mut sq = ring.squeue();

            let mut sqe = sq.get_sqe().unwrap();
            // SAFETY: a no-op reads no pointer and names no descriptor.
            unsafe {
                sqe.prep_nop();
            }

            let num = sq.submit_and_wait(Count(1)).unwrap();
            assert_eq!(num, Count(1));
        }
    }

    mod sqe128
    {
        use super::*;

        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring through liburing, which Miri cannot run"
        )]
        fn new()
        {
            let ring = IoUring::new().unwrap();
            SubmissionQueue::new(&ring);
        }

        mod get_sqe
        {
            use super::*;

            #[test]
            #[cfg_attr(
                miri,
                ignore = "it sets up a ring through liburing, which Miri cannot run"
            )]
            #[should_panic(expected = r#"called `Option::unwrap()` on a `None` value"#)]
            fn none()
            {
                let builder = IoUring::builder().setup_sqe128();
                self::fixture::get_sqe::none(builder);
            }

            #[test]
            #[cfg_attr(
                miri,
                ignore = "it sets up a ring through liburing, which Miri cannot run"
            )]
            fn some()
            {
                let builder = IoUring::builder().setup_sqe128();
                self::fixture::get_sqe::some(builder);
            }
        }

        mod get_sqes
        {
            use super::*;

            #[test]
            #[cfg_attr(
                miri,
                ignore = "it sets up a ring through liburing, which Miri cannot run"
            )]
            #[should_panic(expected = r#"called `Option::unwrap()` on a `None` value"#)]
            fn none()
            {
                let builder = IoUring::builder().setup_sqe128();
                self::fixture::get_sqes::none(builder);
            }

            #[test]
            #[cfg_attr(
                miri,
                ignore = "it sets up a ring through liburing, which Miri cannot run"
            )]
            fn some_one()
            {
                let builder = IoUring::builder().setup_sqe128();
                self::fixture::get_sqes::some_one(builder);
            }

            #[test]
            #[cfg_attr(
                miri,
                ignore = "it sets up a ring through liburing, which Miri cannot run"
            )]
            fn some_many()
            {
                let builder = IoUring::builder().setup_sqe128();
                self::fixture::get_sqes::some_many(builder);
            }
        }
    }
}
