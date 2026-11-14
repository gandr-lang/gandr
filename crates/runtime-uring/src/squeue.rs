use ::core::marker::PhantomData;
use ::core::ptr::NonNull;

use crate::IoUring;
use crate::sqe::Sqes;
use crate::sys::SysResult as _;

#[non_exhaustive]
pub struct SubmissionQueue<'ring, S>
{
    pub(crate) ring: NonNull<::liburing_rs::io_uring>,
    marker: PhantomData<&'ring mut IoUring<'static, S, crate::cqe::kind::Cqe16>>,
}

impl<'ring, S> SubmissionQueue<'ring, S>
where
    S: crate::sqe::Kind,
{
    pub(crate) fn new<C>(ring: &'ring IoUring<S, C>) -> Self
    {
        let ring = NonNull::from(&ring.ring);
        Self {
            ring,
            marker: PhantomData,
        }
    }

    pub fn get_sqe(&mut self) -> Option<crate::sqe::repr::Sqe<'_>>
    {
        // SAFETY: FIXME
        unsafe { crate::sqe::get_sqe_raw::<S>(self.ring) }.map(Into::into)
    }

    pub fn get_sqes(
        &mut self,
        len: u32,
    ) -> Option<Sqes<'_, S>>
    {
        let ring = self.ring.as_ptr();
        // SAFETY:
        let rem = unsafe { ::liburing_rs::io_uring_sq_space_left(ring) };
        if rem < len {
            return None;
        }
        Some(Sqes::new(self, len))
    }

    /// # Errors
    pub fn submit(&mut self) -> ::std::io::Result<u32>
    {
        let ring = self.ring.as_ptr();
        // SAFETY:
        let code = unsafe { ::liburing_rs::io_uring_submit(ring) };
        code.sys_uint()
    }

    /// # Errors
    pub fn submit_and_wait(
        &mut self,
        wait_nr: u32,
    ) -> ::std::io::Result<u32>
    {
        let ring = self.ring.as_ptr();
        // SAFETY:
        let code = unsafe { ::liburing_rs::io_uring_submit_and_wait(ring, wait_nr) };
        code.sys_uint()
    }
}

impl SubmissionQueue<'_, crate::sqe::kind::Sqe128>
{
    pub fn get_sqe128(&mut self) -> Option<crate::sqe::repr::Sqe128<'_>>
    {
        // SAFETY: FIXME
        unsafe { crate::sqe::get_sqe_raw::<crate::sqe::kind::Sqe128>(self.ring) }
    }
}

#[cfg(test)]
pub(crate) mod test
{
    use crate::IoUringBuilder;
    use crate::ring::IoUring;
    use crate::squeue::SubmissionQueue;

    mod fixture
    {
        use super::*;

        pub mod get_sqe
        {

            use super::*;

            #[should_panic(expected = r#"called `Option::unwrap()` on a `None` value"#)]
            pub fn none<S, C, State>(builder: IoUringBuilder<'_, S, C, State>)
            where
                S: crate::sqe::Kind,
                C: crate::cqe::Kind,
                State: crate::ring::io_uring_builder::IsComplete,
                State::Entries: crate::ring::io_uring_builder::IsUnset,
            {
                let mut ring = builder.entries(1).build().unwrap();
                let mut squeue = ring.squeue();
                squeue.get_sqe().unwrap();
                squeue.get_sqe().unwrap();
            }

            pub fn some<S, C, State>(builder: IoUringBuilder<'_, S, C, State>)
            where
                S: crate::sqe::Kind,
                C: crate::cqe::Kind,
                State: crate::ring::io_uring_builder::IsComplete,
                State::Entries: crate::ring::io_uring_builder::IsUnset,
            {
                let mut ring = builder.entries(1).build().unwrap();
                let mut squeue = ring.squeue();
                squeue.get_sqe().unwrap();
            }
        }

        pub mod get_sqes
        {
            use super::*;

            #[should_panic(expected = r#"called `Option::unwrap()` on a `None` value"#)]
            pub fn none<S, C, State>(builder: IoUringBuilder<'_, S, C, State>)
            where
                S: crate::sqe::Kind,
                C: crate::cqe::Kind,
                State: crate::ring::io_uring_builder::IsComplete,
                State::Entries: crate::ring::io_uring_builder::IsUnset,
            {
                let mut ring = builder.entries(1).build().unwrap();
                let mut squeue = ring.squeue();
                let len = 2u32;
                squeue.get_sqes(len).unwrap();
            }

            pub fn some_one<S, C, State>(builder: IoUringBuilder<'_, S, C, State>)
            where
                S: crate::sqe::Kind,
                C: crate::cqe::Kind,
                State: crate::ring::io_uring_builder::IsComplete,
                State::Entries: crate::ring::io_uring_builder::IsUnset,
            {
                let mut ring = builder.entries(1).build().unwrap();
                let mut squeue = ring.squeue();
                let len = 1u32;
                let sqes = squeue.get_sqes(1).unwrap();
                let mut num = 0u32;
                for _ in sqes {
                    num += 1;
                }
                assert_eq!(num, len);
            }

            pub fn some_many<S, C, State>(builder: IoUringBuilder<'_, S, C, State>)
            where
                S: crate::sqe::Kind,
                C: crate::cqe::Kind,
                State: crate::ring::io_uring_builder::IsComplete,
                State::Entries: crate::ring::io_uring_builder::IsUnset,
            {
                let mut ring = builder.entries(1024).build().unwrap();
                let mut squeue = ring.squeue();
                let len = 256u32;
                let sqes = squeue.get_sqes(len).unwrap();
                let mut num = 0u32;
                for _ in sqes {
                    num += 1;
                }
                assert_eq!(num, len);
            }
        }
    }

    mod sqe64
    {
        use super::*;

        #[test]
        fn new()
        {
            let ring = IoUring::new().unwrap();
            SubmissionQueue::new(&ring);
        }

        mod get_sqe
        {
            use super::*;

            #[test]
            #[should_panic(expected = r#"called `Option::unwrap()` on a `None` value"#)]
            fn none()
            {
                let builder = IoUring::builder();
                self::fixture::get_sqe::none(builder);
            }

            #[test]
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
            #[should_panic(expected = r#"called `Option::unwrap()` on a `None` value"#)]
            fn none()
            {
                let builder = IoUring::builder();
                self::fixture::get_sqes::none(builder);
            }

            #[test]
            fn some_one()
            {
                let builder = IoUring::builder();
                self::fixture::get_sqes::some_one(builder);
            }

            #[test]
            fn some_many()
            {
                let builder = IoUring::builder();
                self::fixture::get_sqes::some_many(builder);
            }
        }

        #[test]
        fn submit_and_wait()
        {
            let mut ring = IoUring::new().unwrap();
            let mut sq = ring.squeue();

            let mut sqe = sq.get_sqe().unwrap();
            unsafe { sqe.prep_nop() };

            let num = sq.submit_and_wait(1).unwrap();
            assert_eq!(num, 1);
        }
    }

    mod sqe128
    {
        use super::*;

        #[test]
        fn new()
        {
            let ring = IoUring::new().unwrap();
            SubmissionQueue::new(&ring);
        }

        mod get_sqe
        {
            use super::*;

            #[test]
            #[should_panic(expected = r#"called `Option::unwrap()` on a `None` value"#)]
            fn none()
            {
                let builder = IoUring::builder().setup_sqe128();
                self::fixture::get_sqe::none(builder);
            }

            #[test]
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
            #[should_panic(expected = r#"called `Option::unwrap()` on a `None` value"#)]
            fn none()
            {
                let builder = IoUring::builder().setup_sqe128();
                self::fixture::get_sqes::none(builder);
            }

            #[test]
            fn some_one()
            {
                let builder = IoUring::builder().setup_sqe128();
                self::fixture::get_sqes::some_one(builder);
            }

            #[test]
            fn some_many()
            {
                let builder = IoUring::builder().setup_sqe128();
                self::fixture::get_sqes::some_many(builder);
            }
        }
    }
}
