use ::anyhow::anyhow;
use ::core::cell::RefCell;
use ::core::pin::pin;
use ::core::task::Poll;
use ::gandr_runtime_uring::IoUring;
use ::slab::Slab;

use crate::completion::Cqe;
use crate::scope::Scope;

#[non_exhaustive]
pub struct Runtime
{
    io: IoUring<'static>,
}

impl Runtime
{
    const IO_URING_ENTRIES: usize = 4096;

    pub fn new() -> ::anyhow::Result<Self>
    {
        let io = IoUring::builder().entries(4096).build()?;
        Ok(Self { io })
    }

    const fn noop_cx() -> ::core::task::Context<'static>
    {
        let waker = ::core::task::Waker::noop();
        ::core::task::Context::from_waker(waker)
    }

    pub fn run<'env, T, F>(
        self,
        start: F,
    ) -> ::anyhow::Result<T>
    where
        F: for<'tsk> AsyncFnOnce(&'tsk Scope<'tsk, 'env>) -> T,
    {
        let io = RefCell::new(self.io);
        let tasks = RefCell::new(Slab::default());

        let scope = Scope::new(&io, &tasks);
        let mut future = pin!(start(&scope));

        loop {
            // Check if the main future is ready.
            if let Poll::Ready(val) = future.as_mut().poll(&mut Self::noop_cx()) {
                // The main future never reaches `Poll::Ready` if there are
                // tasks remaining as `Poll::Pending`. This is
                // because tasks are not received by the runtime unless
                // the spawned future is awaited in some enclosing future.
                // Eventually this enclosing future must be the
                // main future which is the only entrypoint to
                // start the runtime. Thus the main future always depends on all
                // received tasks.
                debug_assert_eq!(tasks.borrow().len(), 0, "tasks remaining");

                // Return immediately if the future is ready. See above.
                return Ok(val);
            }

            // Submit the entries that the scope prepared and wait for at
            // least one completion.
            let mut io = io.borrow_mut();
            let (mut squ, mut cqu) = io.queues();
            squ.submit_and_wait(1)?;

            // Process newly completed tasks.
            for cqe in cqu.ready() {
                // Cross-reference the task against the CQE user_data.
                let key = usize::try_from(cqe.user_data())?;

                // Remove the task since it's completed.
                let task = tasks
                    .borrow_mut()
                    .try_remove(key)
                    .ok_or_else(|| anyhow!("task lookup failed: {key}"))?;

                // Forward the CQE to the future's resolver.
                task.cqe_tx
                    .send(Cqe::new(cqe.res(), cqe.flags()))
                    .map_err(|_err| anyhow!("failed to send cqe result for task: {key}"))?;
            }
        }
    }
}

#[cfg(test)]
pub(crate) mod test
{
    #![allow(clippy::unwrap_used, reason = "cfg(test)")]

    use super::*;

    pub mod harness
    {
        use super::*;

        pub fn new() -> Runtime
        {
            Runtime::new().unwrap()
        }
    }

    #[test]
    fn new()
    {
        self::harness::new();
    }

    mod run
    {
        use super::*;

        #[test]
        fn closure()
        {
            let data = &mut vec![];
            crate::test::harness::runtime::new()
                .run(async |scope| {
                    data.push(0u8);
                    Ok::<_, ::anyhow::Error>(())
                })
                .unwrap()
                .unwrap();
            assert_eq!(data.as_slice(), &[0u8]);
        }
    }
}
