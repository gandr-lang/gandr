//! The worker's ring: one `Io` of the IO layer for each thread of the pool,
//! the thread's own as its lane is.
//!
//! A thread opens its ring at its first IO, at the lane's measured depth,
//! and closes it when the thread ends. No other thread reaches it, so no
//! lock guards it. A thread that the kernel refuses a ring runs the blocking
//! form behind the same calls. The worker names the global allocator until
//! it holds a region of its own.

use alloc::alloc::Global;
use core::cell::RefCell;

use gandr_storage_io::Count;
use gandr_storage_io::Errno;
use gandr_storage_io::Io;

use super::lane::DEPTH;

std::thread_local! {
    /// The calling thread's ring, once its first IO opened it.
    static RING: RefCell<Option<Io<Global>>> = const { RefCell::new(None) };
}

/// Run `work` on the calling thread's ring, which the first call on the
/// thread opens at the lane's depth.
///
/// # Specification
/// - ensures: on `Ok`, the result of `work`, which ran once on the ring of the
///   calling thread alone; each later call on the thread reaches the same ring.
/// - fails: [`Errno::BUSY`] when `work` calls again on the thread; the error
///   number of the ring's opening when the kernel refuses it and the blocking
///   form does not follow.
/// - panics: a panic of `work`.
/// - executable: none — the ring is the thread's.
///
/// # Errors
/// [`Errno::BUSY`] for a nested call; the error number of the opening.
///
/// # Adequacy
/// - hypothesis: L3 — the pool's workers each write through their own ring, the
///   file holds each item's bytes, and a nested call is refused.
/// - witness: `pool::ring::tests::each_worker_writes_through_its_own_ring`
#[inline]
pub fn with_ring<Out, Work>(work: Work) -> Result<Out, Errno>
where
    Work: FnOnce(&mut Io<Global>) -> Out,
{
    RING.with(|cell| {
        let mut held = cell.try_borrow_mut().map_err(|_borrowed| Errno::BUSY)?;
        let ring = match *held {
            Some(ref mut ring) => ring,
            None => held.insert(Io::open(depth())?),
        };
        Ok(work(ring))
    })
}

/// The depth of each worker's ring: the lane's measured depth.
///
/// # Specification
/// trivial.
fn depth() -> Count
{
    Count::from(u32::try_from(DEPTH).unwrap_or(u32::MAX))
}

#[cfg(test)]
mod tests
{
    use core::num::NonZeroUsize;
    use std::fs::OpenOptions;

    use gandr_core_fork::Fork as _;
    use gandr_storage_io::Buffer;
    use gandr_storage_io::Chain;
    use gandr_storage_io::Handle;
    use gandr_storage_io::Position;
    use gandr_storage_io::Segment;

    use super::*;
    use crate::Pool;
    use crate::width::Threads;
    use crate::width::Width;

    /// The bytes of each item's block.
    const BLOCK: usize = 512;

    /// The items of a pool of four threads each write their own block of one
    /// file through the ring of the thread that runs them, and wait for it.
    /// The file holds each block. A call inside the work is refused.
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
        let handle = Handle::from(file);
        let pool = Pool::new(Width::Threads(Threads::from(
            NonZeroUsize::new(4_usize).unwrap(),
        )));
        let mut items: Vec<(u8, Option<Result<u32, Errno>>)> =
            (1_u8 ..= 64).map(|byte| (byte, None)).collect();
        pool.each(
            &mut items,
            || (),
            |_state, &mut (byte, ref mut wrote)| {
                let at = u64::from(byte - 1) * u64::try_from(BLOCK).unwrap();
                *wrote = Some(
                    with_ring(|io| {
                        assert_eq!(
                            with_ring(|_again| ()).err(),
                            Some(Errno::BUSY),
                            "a call inside the work is refused"
                        );
                        let mut segment = Segment::new(handle.clone(), Position::from(at));
                        let _append = io
                            .append(&mut segment, Buffer::from(vec![byte; BLOCK]), Chain::Alone)
                            .map_err(|refused| match refused.reason {
                                gandr_storage_io::Reason::Kernel(errno) => errno,
                                gandr_storage_io::Reason::Unread
                                | gandr_storage_io::Reason::Budget => Errno::INVALID,
                            })?;
                        let done = io.wait()?.ok_or(Errno::PROTOCOL)?;
                        done.outcome.map(u32::from)
                    })
                    .and_then(|wrote| wrote),
                );
            },
        );
        assert!(
            items
                .iter()
                .all(|&(_, ref wrote)| *wrote == Some(Ok(u32::try_from(BLOCK).unwrap()))),
            "each item writes its whole block"
        );
        let bytes = std::fs::read(&path).unwrap();
        std::fs::remove_file(&path).unwrap();
        let expected: Vec<u8> = (1_u8 ..= 64)
            .flat_map(|byte| core::iter::repeat_n(byte, BLOCK))
            .collect();
        assert_eq!(bytes, expected, "the file holds each item's block in place");
    }
}
