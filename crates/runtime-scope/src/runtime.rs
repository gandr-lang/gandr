use ::anyhow::anyhow;
use ::core::pin::pin;
use ::core::task::Poll;
use ::io_uring::IoUring;
use ::slab::Slab;

use crate::Receiver;
use crate::Sender;
use crate::scope::Scope;
use crate::submission::Submission;

#[non_exhaustive]
pub struct Runtime
{
    io: IoUring,
}

impl Runtime
{
    const IO_URING_ENTRIES: usize = 4096;

    pub fn new() -> ::anyhow::Result<Self>
    {
        let io = IoUring::new(4096)?;
        Ok(Self { io })
    }

    const fn noop_cx() -> ::core::task::Context<'static>
    {
        let waker = ::core::task::Waker::noop();
        ::core::task::Context::from_waker(waker)
    }

    pub fn run<'env, T, F>(
        mut self,
        start: F,
    ) -> ::anyhow::Result<T>
    where
        F: for<'tsk> AsyncFnOnce(&'tsk Scope<'tsk, 'env>) -> T,
    {
        let (req_tx, req_rx) = ::kanal::unbounded();
        let mut tasks = Slab::default();

        let scope = Scope::new(req_tx.to_async());
        let mut future = pin!(start(&scope));

        let (sub, mut squ, mut cqu) = self.io.split();

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
                debug_assert_eq!(tasks.len(), 0, "tasks remaining");

                // Return immediately if the future is ready. See above.
                return Ok(val);
            }

            // Process newly submitted tasks.
            while let Ok(Some(task)) = req_rx.try_recv_realtime() {
                // SAFETY: [`Task`] SQEs are constructed such that they respect
                // io_uring safety.
                unsafe { squ.push(&task.sqe) }?;
                tasks.insert(task);
            }

            // Synchronize SQE/CQE queues and submit and wait for at least one
            // completion.
            squ.sync();
            sub.submit_and_wait(1)?;
            cqu.sync();

            // Process newly completed tasks.
            for cqe in cqu.by_ref() {
                // Cross-reference the task against the CQE user_data.
                let key = usize::try_from(cqe.user_data())?;

                // Remove the task since it's completed.
                let task = tasks
                    .try_remove(key)
                    .ok_or_else(|| anyhow!("task lookup failed: {key}"))?;

                // Forward the CQE to the future's resolver.
                task.cqe_tx
                    .send(cqe)
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
