//! The heap: blocks in size classes, cut from runs of pages, for one thread.
//!
//! A class holds blocks of one power of two, from 16 bytes to 4 KiB. Each
//! class keeps a list of its free blocks and a cursor into its newest run. An
//! allocation takes the first free block, or the block at the cursor, or the
//! first block of a new run. Only the new run costs a call to the host. A
//! layout past the largest class takes whole pages of its own, and its free
//! gives them back at once.
//!
//! The first block of each run holds the address of the run before it, so
//! the end of the heap gives every run back with no other record. A heap
//! that allocates nothing maps nothing.

use core::alloc::AllocError;
use core::alloc::Allocator;
use core::alloc::Layout;
use core::cell::Cell;
use core::num::NonZeroUsize;
use core::ptr::NonNull;

use crate::EINVAL;
use crate::ENOMEM;
use crate::Operation;
use crate::PageSize;
use crate::Protection;
use crate::Refused;
use crate::sys;

/// The exponent of the smallest class: 16 bytes, room for one address with
/// the alignment of two.
const SMALLEST: u32 = 4;

/// The exponent of the largest class: 4 KiB, the smallest page of a host.
const LARGEST: u32 = 12;

/// The count of classes.
const CLASSES: usize = 9;

/// The bytes of a run when a page is smaller: 64 KiB.
const RUN: NonZeroUsize = NonZeroUsize::new(1_usize << 16_u32).expect("2^16 is not zero");

/// The size class that a layout falls in.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Size
{
    /// A block of the class `index`, which holds blocks of `bytes` bytes.
    Class
    {
        /// The class's place, smallest first.
        index: usize,
        /// The bytes of each block of the class: `2^(index + 4)`.
        bytes: usize,
    },
    /// Whole pages of their own: this many bytes.
    Pages(NonZeroUsize),
}

/// One size class: its free blocks and the cut of its newest run.
///
/// # Specification
/// trivial.
#[derive(Debug)]
struct Class
{
    /// The first free block. Each free block's first word holds the next.
    free: Cell<*mut u8>,
    /// The next block to cut from the newest run.
    cursor: Cell<*mut u8>,
    /// The end of the newest run.
    end: Cell<*mut u8>,
    /// The newest run. Its first word holds the run before it.
    runs: Cell<*mut u8>,
}

impl Class
{
    /// A class with no run and no free block.
    ///
    /// # Specification
    /// trivial.
    const fn new() -> Self
    {
        Self {
            free: Cell::new(core::ptr::null_mut()),
            cursor: Cell::new(core::ptr::null_mut()),
            end: Cell::new(core::ptr::null_mut()),
            runs: Cell::new(core::ptr::null_mut()),
        }
    }
}

/// An allocator of blocks in size classes over runs of whole pages.
///
/// The heap is one thread's: it is not `Sync`, so a shared reference stays on
/// the thread that holds the heap. Its end gives every run back to the host.
/// A block lives no longer than the heap that gives it.
///
/// # Specification
/// trivial.
#[derive(Debug)]
pub struct Heap
{
    /// The host's page size.
    page: PageSize,
    /// The bytes of one run: 64 KiB, or one page when a page is larger.
    run: NonZeroUsize,
    /// The size classes, smallest first.
    classes: [Class; CLASSES],
}

impl Heap
{
    /// A heap over pages of `page` bytes, which maps nothing yet.
    ///
    /// # Specification
    /// - ensures: a heap with no run; its first allocation maps its first run.
    /// - panics: none.
    /// - executable: none — the heap maps nothing until it allocates.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the mapped pages of the process are as many after a
    ///   heap ends as before it started.
    /// - witness: `pages::heap::mixed_blocks_leave_the_mapped_pages_as_they_were`
    #[must_use]
    #[inline]
    pub const fn new(page: PageSize) -> Self
    {
        let run = if page.0.get() > RUN.get() {
            page.0
        }
        else {
            RUN
        };
        Self {
            page,
            run,
            classes: [const { Class::new() }; CLASSES],
        }
    }

    /// The size class of `layout`.
    ///
    /// # Specification
    /// - ensures: the smallest class whose size is at least the layout's size
    ///   and its alignment; past the largest class, the layout's size rounded
    ///   up to whole pages; a refusal under the name `allocate` with `EINVAL`
    ///   for an alignment past a page, or with `ENOMEM` for a size whose pages
    ///   overflow a word.
    /// - panics: none.
    /// - executable: none — a pure function of the layout and the page.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a block of each class keeps its bytes while the
    ///   blocks around it change, and an alignment past a page is refused.
    /// - witness: `tests::heap::each_block_keeps_its_bytes_and_its_alignment`
    fn size(
        &self,
        layout: Layout,
    ) -> Result<Size, Refused>
    {
        let size = layout.size().max(layout.align());
        if size <= 1 << LARGEST {
            let bytes = size.max(1 << SMALLEST).next_power_of_two();
            let index =
                usize::try_from(bytes.trailing_zeros().saturating_sub(SMALLEST)).unwrap_or(CLASSES);
            return Ok(Size::Class { index, bytes });
        }
        if layout.align() > self.page.0.get() {
            return Err(Refused::new(Operation::Allocate, EINVAL));
        }
        size.checked_next_multiple_of(self.page.0.get())
            .and_then(NonZeroUsize::new)
            .map(Size::Pages)
            .ok_or(Refused::new(Operation::Allocate, ENOMEM))
    }

    /// The bytes of a block of the size `size`.
    ///
    /// # Specification
    /// trivial.
    const fn bytes(size: Size) -> usize
    {
        match size {
            Size::Class { bytes, .. } => bytes,
            Size::Pages(bytes) => bytes.get(),
        }
    }

    /// Maps a new run for the class `class` of `bytes`-byte blocks, and cuts
    /// its first block for the record of the run before it.
    ///
    /// # Specification
    /// - ensures: the class's cursor is the run's second block and its end is
    ///   the run's end; or the host's error number under the name `map`, with
    ///   the class unchanged.
    /// - panics: none.
    /// - executable: none — the host decides what it maps.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the blocks of many runs keep their bytes, and the end
    ///   of the heap gives every run back.
    /// - witness: `pages::heap::mixed_blocks_leave_the_mapped_pages_as_they_were`
    fn refill(
        &self,
        class: &Class,
        bytes: usize,
    ) -> Result<(), Refused>
    {
        let run = sys::map(self.run, Protection::ReadWrite)
            .map_err(|number| Refused::host(Operation::Map, number))?;
        // SAFETY: the run is the heap's own, readable and writable, aligned
        // to a page, and its first block holds one address.
        unsafe {
            run.cast::<*mut u8>().write(class.runs.get());
        }
        let base = run.as_ptr();
        class.runs.set(base);
        class.cursor.set(base.wrapping_add(bytes));
        class.end.set(base.wrapping_add(self.run.get()));
        Ok(())
    }

    /// A block for `layout`.
    ///
    /// # Specification
    /// - ensures: a block of at least the layout's size, aligned to the
    ///   layout's alignment, that no other live block of the heap overlaps; its
    ///   length is the size of its class, or its whole pages; a refusal of
    ///   [`Heap::size`]; or the host's error number under the name `map`.
    /// - panics: none.
    /// - executable: none — the host decides what it maps.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a block of each class keeps its bytes while the
    ///   blocks around it change, and its address has its alignment.
    /// - witness: `tests::heap::each_block_keeps_its_bytes_and_its_alignment`
    ///
    /// # Errors
    /// A refusal of the layout's size class, or the host's error number under
    /// the name `map`.
    ///
    /// # Cost
    /// - time: constant for a class; one call to the host for a new run or for
    ///   whole pages.
    #[inline]
    pub fn allocate(
        &self,
        layout: Layout,
    ) -> Result<NonNull<[u8]>, Refused>
    {
        let (index, bytes) = match self.size(layout)? {
            Size::Pages(length) => {
                let base = sys::map(length, Protection::ReadWrite)
                    .map_err(|number| Refused::host(Operation::Map, number))?;
                return Ok(NonNull::slice_from_raw_parts(base, length.get()));
            },
            Size::Class { index, bytes } => (index, bytes),
        };
        let Some(class) = self.classes.get(index)
        else {
            return Err(Refused::new(Operation::Allocate, EINVAL));
        };
        let block = if let Some(free) = NonNull::new(class.free.get()) {
            // SAFETY: a free block's first word holds the next free block.
            class.free.set(unsafe { free.cast::<*mut u8>().read() });
            free
        }
        else {
            if class.cursor.get() == class.end.get() {
                self.refill(class, bytes)?;
            }
            let cursor = class.cursor.get();
            class.cursor.set(cursor.wrapping_add(bytes));
            NonNull::new(cursor).ok_or(Refused::new(Operation::Allocate, ENOMEM))?
        };
        Ok(NonNull::slice_from_raw_parts(block, bytes))
    }

    /// Gives the block at `block` back to the heap.
    ///
    /// # Safety
    ///
    /// - unsafe invariants: the heap gave the block for a layout that `layout`
    ///   fits, and no reference into the block lives.
    ///
    /// # Specification
    /// - ensures: a block of a class is the class's next block; a block of
    ///   whole pages goes back to the host; or the host's error number under
    ///   the name `unmap`.
    /// - panics: none.
    /// - executable: none — the host unmaps whole pages.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — blocks that are freed and taken again keep the bytes
    ///   of the blocks that live.
    /// - witness: `tests::heap::each_block_keeps_its_bytes_and_its_alignment`
    ///
    /// # Errors
    /// A refusal of the layout's size class, or the host's error number under
    /// the name `unmap`.
    ///
    /// # Cost
    /// - time: constant for a class; one call to the host for whole pages.
    #[inline]
    pub unsafe fn free(
        &self,
        block: NonNull<u8>,
        layout: Layout,
    ) -> Result<(), Refused>
    {
        match self.size(layout)? {
            Size::Class { index, .. } => {
                let Some(class) = self.classes.get(index)
                else {
                    return Err(Refused::new(Operation::Allocate, EINVAL));
                };
                // SAFETY: the block is the caller's to give back, and it has
                // room for one address.
                unsafe {
                    block.cast::<*mut u8>().write(class.free.get());
                }
                class.free.set(block.as_ptr());
                Ok(())
            },
            // SAFETY: the block is the caller's to give back, and the heap
            // mapped its pages for it alone.
            Size::Pages(length) => unsafe { sys::unmap(block, length) }
                .map_err(|number| Refused::host(Operation::Unmap, number)),
        }
    }

    /// Grows the block at `block` from the layout `old` to the layout `new`.
    ///
    /// # Safety
    ///
    /// - unsafe invariants: the heap gave the block for a layout that `old`
    ///   fits; `new` is at least as large as `old`; and no reference into the
    ///   block lives.
    ///
    /// # Specification
    /// - ensures: the same block when `new` falls in the size of `old`;
    ///   otherwise a new block with the first bytes of the old one, and the old
    ///   block given back; or a refusal of [`Heap::allocate`], with the old
    ///   block unchanged.
    /// - panics: none.
    /// - executable: none — the host decides what it maps.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a block that grows within its class keeps its
    ///   address, and a block that grows past it keeps its bytes.
    /// - witness: `tests::heap::a_grown_block_keeps_its_bytes`
    ///
    /// # Errors
    /// A refusal of [`Heap::allocate`] or of [`Heap::free`].
    #[inline]
    pub unsafe fn grow(
        &self,
        block: NonNull<u8>,
        old: Layout,
        new: Layout,
    ) -> Result<NonNull<[u8]>, Refused>
    {
        let size = self.size(old)?;
        if self.size(new)? == size {
            return Ok(NonNull::slice_from_raw_parts(block, Self::bytes(size)));
        }
        let grown = self.allocate(new)?;
        // SAFETY: the old block holds `old.size()` bytes, the new block holds
        // at least as many, and two blocks of the heap never overlap.
        unsafe {
            core::ptr::copy_nonoverlapping(block.as_ptr(), grown.cast::<u8>().as_ptr(), old.size());
        }
        // SAFETY: the caller's invariants hold for the old block.
        unsafe { self.free(block, old) }?;
        Ok(grown)
    }
}

impl Drop for Heap
{
    /// Gives each run of each class back to the host.
    ///
    /// # Specification
    /// - ensures: no run of the heap stays mapped.
    /// - panics: none.
    /// - executable: none — the host unmaps the runs.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the mapped pages of the process are as many after a
    ///   heap ends as before it started.
    /// - witness: `pages::heap::mixed_blocks_leave_the_mapped_pages_as_they_were`
    #[inline]
    fn drop(&mut self)
    {
        for class in &self.classes {
            let mut run = class.runs.get();
            while let Some(base) = NonNull::new(run) {
                // SAFETY: a run's first word holds the run before it.
                run = unsafe { base.cast::<*mut u8>().read() };
                // SAFETY: the heap ends, so no block of the run lives.
                let _unmapped = unsafe { sys::unmap(base, self.run) };
            }
        }
    }
}

// SAFETY: a block stays valid while the heap lives, a copy of the reference
// names the same heap, and two live blocks never overlap.
unsafe impl Allocator for &Heap
{
    /// The heap's [`Heap::allocate`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn allocate(
        &self,
        layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError>
    {
        Heap::allocate(self, layout).map_err(|_refused| AllocError)
    }

    /// The heap's [`Heap::free`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    unsafe fn deallocate(
        &self,
        ptr: NonNull<u8>,
        layout: Layout,
    )
    {
        // SAFETY: the trait's contract is the caller's.
        let _freed = unsafe { Heap::free(self, ptr, layout) };
    }

    /// The heap's [`Heap::grow`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError>
    {
        // SAFETY: the trait's contract is the caller's.
        unsafe { Heap::grow(self, ptr, old_layout, new_layout) }.map_err(|_refused| AllocError)
    }
}
