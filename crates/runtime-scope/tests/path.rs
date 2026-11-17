//! One request's path, from `Scope::request` to the completion's hand-back,
//! allocates nothing after the start of a run.

#![cfg(target_os = "linux")]

use ::core::alloc::GlobalAlloc;
use ::core::alloc::Layout;
use ::core::cell::Cell;
use ::gandr_runtime_scope::Depth;
use ::gandr_runtime_scope::Runtime;
use ::gandr_runtime_uring::Sqe64;
use ::std::alloc::System;

::std::thread_local! {
    /// The allocations of this thread.
    static ALLOCATIONS: Cell<usize> = const { Cell::new(0) };
}

/// The system's allocator, which counts each allocation of a thread.
struct Counting;

/// The allocator face of the count: each call goes to the system's
/// allocator.
///
/// # Safety
/// - unsafe invariants: each method forwards to the system's allocator with the
///   caller's arguments, so each block is a block of the system's allocator.
///   The count touches no memory of a block.
// SAFETY: the invariants above hold: each body calls `System` with its own
// arguments, and the count is a cell of the thread.
unsafe impl GlobalAlloc for Counting
{
    /// A block of `layout` from the system's allocator, counted.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Safety
    /// - unsafe invariants: the caller's, as `GlobalAlloc::alloc` states; the
    ///   body passes them to `System` whole.
    unsafe fn alloc(
        &self,
        layout: Layout,
    ) -> *mut u8
    {
        ALLOCATIONS.with(|count| count.set(count.get().saturating_add(1)));
        // SAFETY: the caller's layout, as `GlobalAlloc::alloc` states.
        unsafe { System.alloc(layout) }
    }

    /// The block back to the system's allocator.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Safety
    /// - unsafe invariants: the caller's, as `GlobalAlloc::dealloc` states; the
    ///   body passes them to `System` whole.
    unsafe fn dealloc(
        &self,
        ptr: *mut u8,
        layout: Layout,
    )
    {
        // SAFETY: the caller's block and layout, as `GlobalAlloc::dealloc`
        // states.
        unsafe { System.dealloc(ptr, layout) }
    }

    /// The block grown or shrunk by the system's allocator, counted.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Safety
    /// - unsafe invariants: the caller's, as `GlobalAlloc::realloc` states; the
    ///   body passes them to `System` whole.
    unsafe fn realloc(
        &self,
        ptr: *mut u8,
        layout: Layout,
        new_size: usize,
    ) -> *mut u8
    {
        ALLOCATIONS.with(|count| count.set(count.get().saturating_add(1)));
        // SAFETY: the caller's block, layout and size, as
        // `GlobalAlloc::realloc` states.
        unsafe { System.realloc(ptr, layout, new_size) }
    }
}

#[global_allocator]
static GLOBAL: Counting = Counting;

#[cfg(test)]
mod request
{
    use super::*;

    /// A thousand no-ops through the scope, after one that warms the path,
    /// make no allocation of the thread.
    #[test]
    #[cfg_attr(
        miri,
        ignore = "it sets up a ring of the kernel, which Miri cannot run"
    )]
    fn a_request_allocates_nothing_after_the_start()
    {
        let nop = |sqe: &mut Sqe64<'_>| {
            // SAFETY: a no-op reads no pointer and names no descriptor.
            unsafe {
                sqe.prep_nop();
            }
        };
        let mut runtime = Runtime::with_depth(Depth::from(4096_u16)).unwrap();
        let made = runtime
            .run(async |scope| {
                scope.request(nop).await.unwrap();
                let before = ALLOCATIONS.with(Cell::get);
                for _request in 0 .. 1_000_u16 {
                    scope.request(nop).await.unwrap();
                }
                ALLOCATIONS.with(Cell::get).saturating_sub(before)
            })
            .unwrap();
        assert_eq!(made, 0);
    }

    /// A second run of one runtime, with a no-op in it, makes no allocation
    /// of the thread: the runtime keeps its ring and its table.
    #[test]
    #[cfg_attr(
        miri,
        ignore = "it sets up a ring of the kernel, which Miri cannot run"
    )]
    fn a_later_run_allocates_nothing()
    {
        let nop = |sqe: &mut Sqe64<'_>| {
            // SAFETY: a no-op reads no pointer and names no descriptor.
            unsafe {
                sqe.prep_nop();
            }
        };
        let mut runtime = Runtime::with_depth(Depth::from(8_u16)).unwrap();
        runtime
            .run(async |scope| scope.request(nop).await.unwrap())
            .unwrap();
        let before = ALLOCATIONS.with(Cell::get);
        runtime
            .run(async |scope| scope.request(nop).await.unwrap())
            .unwrap();
        let made = ALLOCATIONS.with(Cell::get).saturating_sub(before);
        assert_eq!(made, 0);
    }
}
