use ::core::cell::RefCell;
use ::core::pin::pin;
use ::core::task::Poll;
use ::gandr_runtime_uring::IoUring;
use ::rustix::io::Errno;

use crate::completion::Cqe;
use crate::error::RuntimeError;
use crate::scope::Scope;
use crate::submission::Table;

#[non_exhaustive]
pub struct Runtime
{
    io: IoUring<'static>,
}

impl Runtime
{
    const IO_URING_ENTRIES: u16 = 4096;

    #[inline]
    pub fn new() -> Result<Self, RuntimeError>
    {
        let io = IoUring::builder()
            .entries(u32::from(Self::IO_URING_ENTRIES))
            .build()?;
        Ok(Self { io })
    }

    const fn noop_cx() -> ::core::task::Context<'static>
    {
        let waker = ::core::task::Waker::noop();
        ::core::task::Context::from_waker(waker)
    }

    #[inline]
    pub fn run<'env, T, F>(
        self,
        start: F,
    ) -> Result<T, RuntimeError>
    where
        F: for<'tsk> AsyncFnOnce(&'tsk Scope<'tsk, 'env>) -> T,
    {
        let io = RefCell::new(self.io);
        let depth = usize::from(Self::IO_URING_ENTRIES);
        let table = Table::new(depth);

        let scope = Scope::new(&io, &table);
        let mut future = pin!(start(&scope));

        loop {
            // Check if the main future is ready.
            if let Poll::Ready(val) = future.as_mut().poll(&mut Self::noop_cx()) {
                // The main future is ready, and the scope ends with it. Each
                // operation that the kernel still holds is cancelled, and
                // the run waits for every completion before it returns, so
                // the kernel holds no operation of the scope after the run.
                end(&io, &table)?;
                return Ok(val);
            }

            // Submit the entries that the scope prepared, wait for at least
            // one completion, and record each in its slot.
            reap(&io, &table)?;
        }
    }
}

/// The user data of a cancel's own completion, which names no slot.
const CANCEL: u64 = u64::MAX;

/// Ends a scope: submits a cancel for each operation that the kernel holds,
/// then drains every completion, two for each cancel.
fn end(
    io: &RefCell<IoUring<'static>>,
    table: &Table,
) -> Result<(), RuntimeError>
{
    if table.held() == 0 {
        return Ok(());
    }
    {
        let mut ring = io.borrow_mut();
        let mut squ = ring.squeue();
        // The kernel takes every prepared entry, so the queue has room for a
        // cancel of each slot that the table holds.
        squ.submit()?;
        for key in table.in_kernel() {
            let data = u64::try_from(key).map_err(|_overflow| RuntimeError::Unknown(CANCEL))?;
            let mut sqe = squ.get_sqe().ok_or(RuntimeError::Full)?;
            // SAFETY: a cancel by user data reads no pointer and names no
            // descriptor.
            unsafe {
                sqe.prep_cancel64(data, 0);
            }
            // SAFETY: the user data is a number that the kernel only hands
            // back.
            unsafe {
                sqe.set_data64(CANCEL);
            }
        }
    }
    while table.held() > 0 {
        reap(io, table)?;
    }
    Ok(())
}

/// Submits the prepared entries, waits for at least one completion, and
/// records each ready completion in its slot of `table`.
pub fn reap(
    io: &RefCell<IoUring<'static>>,
    table: &Table,
) -> Result<(), RuntimeError>
{
    let mut io = io.borrow_mut();
    let (mut squ, mut cqu) = io.queues();
    squ.submit_and_wait(1)?;

    // Process newly completed tasks.
    for cqe in cqu.ready() {
        let data = cqe.user_data();
        if data == CANCEL {
            // A cancel finds its operation, or finds it already complete or
            // past the point of a cancel; the operation's own completion
            // follows in each case. Any other refusal is the kernel's error.
            let res = cqe.res();
            if res.is_negative() {
                let errno = Errno::from_raw_os_error(res.saturating_neg());
                if errno != Errno::NOENT && errno != Errno::ALREADY {
                    return Err(RuntimeError::Kernel(errno));
                }
            }
            continue;
        }
        let key = usize::try_from(data).map_err(|_overflow| RuntimeError::Unknown(data))?;
        if !table.complete(key, Cqe::new(cqe.res(), cqe.flags())) {
            return Err(RuntimeError::Unknown(data));
        }
    }
    Ok(())
}

#[cfg(test)]
pub mod test
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
                    Ok::<_, RuntimeError>(())
                })
                .unwrap()
                .unwrap();
            assert_eq!(data.as_slice(), &[0u8]);
        }

        /// A request past the table's depth waits for a drain. When the
        /// drain frees no slot, because every completion still waits for its
        /// reader, the request gives the stated result of a full table. Once
        /// the completions drop, their slots come free again.
        #[test]
        fn full()
        {
            let nop = |sqe: &mut ::gandr_runtime_uring::Sqe64<'_>| {
                // SAFETY: a no-op reads no pointer and names no descriptor.
                unsafe {
                    sqe.prep_nop();
                }
            };
            let depth = usize::from(Runtime::IO_URING_ENTRIES);
            crate::test::harness::runtime::new()
                .run(async |scope| {
                    let held = ::core::iter::repeat_with(|| scope.request(nop))
                        .take(depth)
                        .collect::<Vec<_>>();
                    let error = scope.request(nop).await.err();
                    assert_eq!(error, Some(RuntimeError::Full));
                    drop(held);
                    scope.request(nop).await.unwrap();
                })
                .unwrap();
        }
    }
}
