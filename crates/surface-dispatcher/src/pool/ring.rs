//! The worker's ring: one `Runtime` of the scoped runtime for each thread of
//! the pool, the thread's own as its lane is.
//!
//! A thread opens its runtime at its first IO, at the lane's measured depth,
//! and closes it when the thread ends. No other thread reaches it, so no
//! lock guards it. A run that fails spends the runtime: the thread drops it,
//! and its next call opens a new one.

use core::cell::RefCell;

use gandr_runtime_scope::Depth;
use gandr_runtime_scope::Runtime;
use gandr_runtime_scope::RuntimeError;
use gandr_runtime_scope::Scope;
use rustix::io::Errno;

use super::lane::DEPTH;

std::thread_local! {
    /// The calling thread's runtime, once its first IO opened it.
    static RING: RefCell<Option<Runtime>> = const { RefCell::new(None) };
}

/// Run `work` as one scope on the calling thread's runtime, which the first
/// call on the thread opens at the lane's depth.
///
/// # Specification
/// - ensures: on `Ok`, the output of `work`, which ran once as a scope on the
///   runtime of the calling thread alone, and the kernel holds no operation of
///   the scope; each later call on the thread reaches the same runtime, until a
///   run fails.
/// - fails: `Kernel(Errno::BUSY)` when `work` calls again on the thread; the
///   error of the runtime's opening when the kernel refuses its ring; the error
///   of the run, after which the thread drops the runtime and its next call
///   opens a new one.
/// - panics: a panic of `work`.
/// - executable: none — the runtime is the thread's.
///
/// # Errors
/// [`RuntimeError::Kernel`] with [`Errno::BUSY`] for a nested call; the error
/// of the opening; the error of the run.
///
/// # Adequacy
/// - hypothesis: L3 — the pool's workers each write through their own runtime,
///   the file holds each item's bytes, and a nested call is refused.
/// - witness: `pool::ring::tests::each_worker_writes_through_its_own_ring`
///
/// # Cost
/// - allocation: the runtime's table of slots at the thread's first call, and
///   again after a run that fails, setup
#[inline]
pub fn with_ring<'env, Out, Work>(work: Work) -> Result<Out, RuntimeError>
where
    Work: for<'tsk> AsyncFnOnce(&'tsk Scope<'tsk, 'env>) -> Out,
{
    RING.with(|cell| {
        let mut held = cell
            .try_borrow_mut()
            .map_err(|_borrowed| RuntimeError::Kernel(Errno::BUSY))?;
        let runtime = match *held {
            Some(ref mut runtime) => runtime,
            None => held.insert(Runtime::with_depth(depth())?),
        };
        let ran = runtime.run(work);
        if ran.is_err() {
            *held = None;
        }
        ran
    })
}

/// The depth of each worker's runtime: the lane's measured depth.
///
/// # Specification
/// trivial.
fn depth() -> Depth
{
    Depth::from(u16::try_from(DEPTH).unwrap_or(u16::MAX))
}

#[cfg(test)]
mod tests
{
    use core::num::NonZeroUsize;
    use std::fs::OpenOptions;
    use std::os::fd::AsRawFd as _;

    use gandr_core_fork::Fork as _;
    use gandr_runtime_uring::arg::Fd;
    use gandr_runtime_uring::arg::Len;
    use gandr_runtime_uring::arg::Offset;

    use super::*;
    use crate::Pool;
    use crate::width::Threads;
    use crate::width::Width;

    /// The bytes of each item's block.
    const BLOCK: u16 = 512;

    /// The items of a pool of four threads each write their own block of one
    /// file through the runtime of the thread that runs them, and wait for
    /// it. The file holds each block. A call inside the work is refused.
    #[test]
    fn each_worker_writes_through_its_own_ring()
    {
        let path =
            std::env::temp_dir().join(format!("gandr-dispatcher-ring-{}", std::process::id()));
        let file = OpenOptions::new()
            .create(true)
            .truncate(true)
            .read(true)
            .write(true)
            .open(&path)
            .unwrap();
        let fd = Fd(file.as_raw_fd());
        let pool = Pool::new(Width::Threads(Threads::from(
            NonZeroUsize::new(4_usize).unwrap(),
        )));
        let mut items: Vec<(u8, Option<Result<usize, RuntimeError>>)> =
            (1_u8 ..= 64).map(|byte| (byte, None)).collect();
        pool.each(
            &mut items,
            || (),
            |_state, &mut (byte, ref mut wrote)| {
                let at = u64::from(byte - 1) * u64::from(BLOCK);
                let block = vec![byte; usize::from(BLOCK)];
                *wrote = Some(
                    with_ring(async |scope| {
                        assert_eq!(
                            with_ring(async |_again| ()).err(),
                            Some(RuntimeError::Kernel(Errno::BUSY)),
                            "a call inside the work is refused"
                        );
                        let write = scope.request(|sqe| {
                            // SAFETY: `block` and `file` outlive the scope,
                            // whose end drains the write.
                            unsafe {
                                sqe.prep_write(
                                    fd,
                                    block.as_ptr().cast(),
                                    Len(u32::from(BLOCK)),
                                    Offset(at),
                                );
                            }
                        });
                        write.await?.count().map(usize::from)
                    })
                    .and_then(|wrote| wrote),
                );
            },
        );
        assert!(
            items
                .iter()
                .all(|&(_, ref wrote)| *wrote == Some(Ok(usize::from(BLOCK)))),
            "each item writes its whole block"
        );
        drop(file);
        let bytes = std::fs::read(&path).unwrap();
        std::fs::remove_file(&path).unwrap();
        let expected: Vec<u8> = (1_u8 ..= 64)
            .flat_map(|byte| core::iter::repeat_n(byte, usize::from(BLOCK)))
            .collect();
        assert_eq!(bytes, expected, "the file holds each item's block in place");
    }
}
