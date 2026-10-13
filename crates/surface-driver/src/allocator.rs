//! The process's global allocator.
//!
//! On macOS, with the `malloc-zone` feature (off by default), every Rust
//! allocation is served by one private malloc zone, `zone::Zone`, instead of
//! the default zone the system allocator calls `malloc` and `free` through.
//! Both zones are the system's own xzone malloc with its hardening; the default
//! zone alone runs its per-thread caches, which a fork that allocates on its
//! workers and frees on the calling thread pays for on every block. Without the
//! feature, and on every other target, the process keeps the system allocator.
//! The choice, its alternatives and its reversal follow.
//!
//! # The global allocator
//!
//! `cargo build -p gandr-lang --features malloc-zone` installs, on macOS, a
//! global allocator over one private malloc zone (`malloc_create_zone`) in
//! place of the default zone; without the feature, and on every other target,
//! the process keeps the system allocator. Both zones are the system's xzone
//! malloc; the default zone alone runs per-thread caches, which `check`'s fork
//! pays for on every block its workers allocate and the calling thread frees.
//! The feature adds no dependency and about 1.2 KB of binary. Its module is the
//! tree's one use of `unsafe`, and its items are the one executable exemption:
//! a predicate evaluated inside the allocator could panic, and a panic must not
//! unwind out of it. `allocator::tests` allocates, clears, grows and shrinks
//! blocks at alignments from 1 byte to 16 KiB through it.
//!
//! The feature is off by default because it misses the kill line set before it
//! was measured: `check` at the default width under 12 ms with the serial run
//! within 3% and peak RSS within 10%. mimalloc, jemalloc and snmalloc were the
//! alternatives: each reached a similar wall at 1.8–2.2× the peak RSS and a C
//! or C++ build, and none moved the Linux wall. Turn the feature on by default
//! when a measurement on a quiet host meets that line; take a crate instead if
//! a Linux measurement shows the system allocator costing a wall a crate
//! removes.

/// The private malloc zone and the global allocator over it.
#[cfg(all(feature = "malloc-zone", target_os = "macos"))]
pub mod zone
{
    use core::alloc::GlobalAlloc;
    use core::alloc::Layout;
    use core::ffi::c_void;
    use core::sync::atomic::AtomicPtr;
    use core::sync::atomic::Ordering;

    /// The alignment every block `malloc_zone_malloc` returns has, as the
    /// system allocator assumes of `malloc` on 64-bit Apple targets.
    const MIN_ALIGN: usize = 16;

    /// A `malloc_zone_t *`: a zone [`malloc_create_zone`] returned, or null.
    #[derive(Clone, Copy)]
    #[repr(transparent)]
    struct ZonePtr(*mut c_void);

    /// A byte count crossing the zone interface: `size_t` or `vm_size_t`.
    #[derive(Clone, Copy)]
    #[repr(transparent)]
    struct Bytes(usize);

    /// A block alignment in bytes: a power of two at least a pointer's width.
    #[derive(Clone, Copy)]
    #[repr(transparent)]
    struct Alignment(usize);

    /// A count of equal items, `malloc_zone_calloc`'s first operand.
    #[derive(Clone, Copy)]
    #[repr(transparent)]
    struct Items(usize);

    /// `malloc_create_zone`'s flags; the driver passes none.
    #[derive(Clone, Copy)]
    #[repr(transparent)]
    struct ZoneFlags(u32);

    /// The zone functions `<malloc/malloc.h>` declares, every one in the
    /// system library since macOS 10.6.
    ///
    /// # Safety
    /// - unsafe invariants: each signature matches its declaration in
    ///   `<malloc/malloc.h>` — the transparent wrappers carry `malloc_zone_t
    ///   *`, `size_t`, `vm_size_t` and `unsigned`, and blocks are `void *` —
    ///   and every zone passed is one [`malloc_create_zone`] returned and that
    ///   has not been destroyed.
    #[expect(
        unused_doc_comments,
        reason = "the policy lint reads this block's safety section; rustdoc renders none on an extern block"
    )]
    unsafe extern "C" {
        /// Create and register a zone with the system's default behaviour.
        ///
        /// # Specification
        /// - ensures: returns a new zone, or null when none can be made;
        ///   `start_size` is unused.
        /// - panics: none.
        /// - executable: none — a foreign declaration has no body to check.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — the first allocation of every test process
        ///   creates the zone that serves the witnesses.
        /// - witness: `allocator::tests::every_alignment_is_served_aligned`
        safe fn malloc_create_zone(
            start_size: Bytes,
            flags: ZoneFlags,
        ) -> ZonePtr;

        /// Destroy `zone` and everything allocated from it.
        ///
        /// # Specification
        /// - requires: `zone` is live and nothing allocated from it is used
        ///   again.
        /// - ensures: `zone` and its blocks are returned to the system.
        /// - panics: none.
        /// - executable: none — a foreign declaration has no body to check.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — reached only by a thread that loses the race to
        ///   create the zone, which the single-threaded start of a process
        ///   never does; review checks the call.
        /// - witness: `allocator::tests::every_alignment_is_served_aligned`
        fn malloc_destroy_zone(zone: ZonePtr);

        /// `size` bytes from `zone`.
        ///
        /// # Specification
        /// - requires: `zone` is live.
        /// - ensures: returns null, or a block of at least `size` bytes at a
        ///   multiple of 16.
        /// - panics: none.
        /// - executable: none — a foreign declaration has no body to check.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — as [`Zone::alloc`].
        /// - witness: `allocator::tests::every_alignment_is_served_aligned`
        fn malloc_zone_malloc(
            zone: ZonePtr,
            size: Bytes,
        ) -> *mut c_void;

        /// `num_items * size` cleared bytes from `zone`.
        ///
        /// # Specification
        /// - requires: `zone` is live.
        /// - ensures: returns null, or a block of at least `num_items * size`
        ///   zero bytes at a multiple of 16.
        /// - panics: none.
        /// - executable: none — a foreign declaration has no body to check.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — as [`Zone::alloc_zeroed`].
        /// - witness: `allocator::tests::zeroed_blocks_read_zero_after_reuse`
        fn malloc_zone_calloc(
            zone: ZonePtr,
            num_items: Items,
            size: Bytes,
        ) -> *mut c_void;

        /// `size` bytes from `zone` at a multiple of `alignment`.
        ///
        /// # Specification
        /// - requires: `zone` is live; `alignment` is a power of two at least a
        ///   pointer's width.
        /// - ensures: returns null, or a block of at least `size` bytes at a
        ///   multiple of `alignment`.
        /// - panics: none.
        /// - executable: none — a foreign declaration has no body to check.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — as [`Zone::alloc`].
        /// - witness: `allocator::tests::every_alignment_is_served_aligned`
        fn malloc_zone_memalign(
            zone: ZonePtr,
            alignment: Alignment,
            size: Bytes,
        ) -> *mut c_void;

        /// `ptr`'s block resized to `size` bytes.
        ///
        /// # Specification
        /// - requires: `zone` is live and `ptr` a live block of it.
        /// - ensures: returns null and leaves `ptr` live, or a block of at
        ///   least `size` bytes at a multiple of 16 holding `ptr`'s contents up
        ///   to the smaller size, and `ptr` is no longer live.
        /// - panics: none.
        /// - executable: none — a foreign declaration has no body to check.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — as [`Zone::realloc`].
        /// - witness: `allocator::tests::reallocation_keeps_contents_and_alignment`
        fn malloc_zone_realloc(
            zone: ZonePtr,
            ptr: *mut c_void,
            size: Bytes,
        ) -> *mut c_void;

        /// Return `ptr`'s block to `zone`.
        ///
        /// # Specification
        /// - requires: `zone` is live and `ptr` a live block of it.
        /// - ensures: the block is the zone's again.
        /// - panics: none.
        /// - executable: none — a foreign declaration has no body to check.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — as [`Zone::dealloc`].
        /// - witness: `allocator::tests::every_alignment_is_served_aligned`
        fn malloc_zone_free(
            zone: ZonePtr,
            ptr: *mut c_void,
        );
    }

    /// The private zone, null until the first allocation creates it.
    static ZONE: AtomicPtr<c_void> = AtomicPtr::new(core::ptr::null_mut());

    /// The private zone, created by the first call.
    ///
    /// # Specification
    /// - ensures: every call returns the same zone once one call has created
    ///   it; a thread that loses the race to publish its own zone destroys it
    ///   unused. The result is null only while no zone could be created, and
    ///   every allocation then fails.
    /// - panics: none.
    /// - executable: none — a predicate evaluated inside the global allocator
    ///   could panic, and a panic must not unwind out of an allocator.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every allocation of the test process reaches the zone
    ///   through this function; a second zone, or a zone dropped while in use,
    ///   frees a block into a zone that does not own it and fails the process.
    /// - witness: `allocator::tests::every_alignment_is_served_aligned`
    /// - witness: `allocator::tests::reallocation_keeps_contents_and_alignment`
    fn zone() -> ZonePtr
    {
        let current = ZONE.load(Ordering::Acquire);
        if !current.is_null() {
            return ZonePtr(current);
        }
        let fresh = malloc_create_zone(Bytes(0), ZoneFlags(0));
        match ZONE.compare_exchange(
            core::ptr::null_mut(),
            fresh.0,
            Ordering::AcqRel,
            Ordering::Acquire,
        ) {
            | Ok(_) => fresh,
            | Err(published) => {
                if !fresh.0.is_null() {
                    // SAFETY: `fresh` came from `malloc_create_zone`, was
                    // never published, and nothing was allocated from it.
                    unsafe {
                        malloc_destroy_zone(fresh);
                    }
                }
                ZonePtr(published)
            },
        }
    }

    /// The global allocator over the private zone.
    ///
    /// # Specification
    /// - ensures: serves every request as [`GlobalAlloc`] requires, from one
    ///   zone the process creates at its first allocation and never destroys.
    /// - provides: the allocator the `gandr` binary installs on macOS under
    ///   `malloc-zone`.
    #[derive(Clone, Copy, Debug)]
    pub struct Zone;

    /// The private zone serves every allocation and takes every block back.
    ///
    /// # Safety
    /// - unsafe invariants: every block handed out is a live block of the
    ///   private zone at least `layout.size()` bytes long at a multiple of
    ///   `layout.align()`, every block taken back is returned to that same
    ///   zone, and no method unwinds.
    // SAFETY: every method serves or takes back blocks of the one private zone
    // at the layout's size and alignment, and none of them can panic.
    unsafe impl GlobalAlloc for Zone
    {
        /// `layout.size()` bytes from the zone at a multiple of
        /// `layout.align()`.
        ///
        /// # Specification
        /// - requires: `layout` has a nonzero size.
        /// - ensures: returns null when the zone cannot serve the request, and
        ///   otherwise the start of `layout.size()` writable bytes at a
        ///   multiple of `layout.align()` that no other live block overlaps. An
        ///   alignment of at most 16 and at most the size takes
        ///   `malloc_zone_malloc`'s 16-byte alignment; any other takes
        ///   `malloc_zone_memalign` at the alignment, raised to a pointer's
        ///   width.
        /// - panics: none.
        /// - executable: none — a predicate evaluated inside the global
        ///   allocator could panic, and a panic must not unwind out of an
        ///   allocator.
        ///
        /// # Safety
        /// - unsafe invariants: the caller upholds [`GlobalAlloc::alloc`]'s
        ///   contract: `layout` has a nonzero size.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — alignments from 1 to 16 KiB at sizes below, at
        ///   and above the alignment, so both branches and their boundary at 16
        ///   are reached; each block is checked aligned and written whole. A
        ///   wrong branch or a dropped alignment returns a misaligned block.
        /// - witness: `allocator::tests::every_alignment_is_served_aligned`
        #[inline]
        unsafe fn alloc(
            &self,
            layout: Layout,
        ) -> *mut u8
        {
            let size = Bytes(layout.size());
            if layout.align() <= MIN_ALIGN && layout.align() <= layout.size() {
                // SAFETY: the zone is live.
                unsafe { malloc_zone_malloc(zone(), size) }.cast()
            }
            else {
                let alignment = Alignment(layout.align().max(size_of::<usize>()));
                // SAFETY: the zone is live and `alignment` is a power of two
                // at least a pointer's width.
                unsafe { malloc_zone_memalign(zone(), alignment, size) }.cast()
            }
        }

        /// `layout.size()` cleared bytes from the zone at a multiple of
        /// `layout.align()`.
        ///
        /// # Specification
        /// - requires: `layout` has a nonzero size.
        /// - ensures: as [`Zone::alloc`], with every byte of the block zero.
        ///   The `malloc_zone_malloc` branch takes `malloc_zone_calloc`; the
        ///   other clears the block it allocates.
        /// - panics: none.
        /// - executable: none — a predicate evaluated inside the global
        ///   allocator could panic, and a panic must not unwind out of an
        ///   allocator.
        ///
        /// # Safety
        /// - unsafe invariants: the caller upholds
        ///   [`GlobalAlloc::alloc_zeroed`]'s contract: `layout` has a nonzero
        ///   size.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — each layout allocates 64 blocks, fills and frees
        ///   them, then allocates 64 cleared blocks, so a reused block left
        ///   uncleared reads nonzero. xzone malloc clears blocks under 1 KiB
        ///   when they are freed, so the page-aligned layouts of 2 KiB and more
        ///   are the ones that distinguish it; alignment is checked as for
        ///   [`Zone::alloc`].
        /// - witness: `allocator::tests::zeroed_blocks_read_zero_after_reuse`
        #[inline]
        unsafe fn alloc_zeroed(
            &self,
            layout: Layout,
        ) -> *mut u8
        {
            if layout.align() <= MIN_ALIGN && layout.align() <= layout.size() {
                // SAFETY: the zone is live.
                unsafe { malloc_zone_calloc(zone(), Items(1), Bytes(layout.size())) }.cast()
            }
            else {
                // SAFETY: the caller's layout has a nonzero size.
                let block = unsafe { self.alloc(layout) };
                if !block.is_null() {
                    // SAFETY: `block` starts `layout.size()` writable bytes.
                    unsafe {
                        block.write_bytes(0, layout.size());
                    }
                }
                block
            }
        }

        /// Return `ptr`'s block to the zone.
        ///
        /// # Specification
        /// - requires: `ptr` is a live block this allocator returned for
        ///   `layout`.
        /// - ensures: the block is the zone's again.
        /// - panics: none.
        /// - executable: none — a predicate evaluated inside the global
        ///   allocator could panic, and a panic must not unwind out of an
        ///   allocator.
        ///
        /// # Safety
        /// - unsafe invariants: the caller upholds [`GlobalAlloc::dealloc`]'s
        ///   contract: `ptr` is live and was allocated by this allocator with
        ///   `layout`.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — every witness frees what it allocates, from every
        ///   branch; a block freed into the wrong zone, or twice, aborts the
        ///   test process.
        /// - witness: `allocator::tests::every_alignment_is_served_aligned`
        /// - witness: `allocator::tests::zeroed_blocks_read_zero_after_reuse`
        #[inline]
        unsafe fn dealloc(
            &self,
            ptr: *mut u8,
            _layout: Layout,
        )
        {
            // SAFETY: `ptr` is a live block of the zone.
            unsafe {
                malloc_zone_free(zone(), ptr.cast());
            }
        }

        /// `ptr`'s block resized to `new_size` bytes at `layout.align()`.
        ///
        /// # Specification
        /// - requires: `ptr` is a live block this allocator returned for
        ///   `layout`; `new_size` is nonzero and, rounded up to
        ///   `layout.align()`, at most `isize::MAX`.
        /// - ensures: returns null and leaves `ptr` live when the zone cannot
        ///   serve the request; otherwise a block of `new_size` bytes at a
        ///   multiple of `layout.align()` whose first `min(layout.size(),
        ///   new_size)` bytes are `ptr`'s, and `ptr` is no longer live. An
        ///   alignment of at most 16 and at most the new size takes
        ///   `malloc_zone_realloc`; any other allocates, copies and frees.
        /// - panics: none.
        /// - executable: none — a predicate evaluated inside the global
        ///   allocator could panic, and a panic must not unwind out of an
        ///   allocator.
        ///
        /// # Safety
        /// - unsafe invariants: the caller upholds [`GlobalAlloc::realloc`]'s
        ///   contract on `ptr`, `layout` and `new_size`.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — each alignment class grows and shrinks a
        ///   patterned block, so a wrong branch, a short or long copy, or a
        ///   lost alignment changes the bytes or the address read back.
        /// - witness: `allocator::tests::reallocation_keeps_contents_and_alignment`
        #[inline]
        unsafe fn realloc(
            &self,
            ptr: *mut u8,
            layout: Layout,
            new_size: usize,
        ) -> *mut u8
        {
            if layout.align() <= MIN_ALIGN && layout.align() <= new_size {
                // SAFETY: `ptr` is a live block of the zone.
                return unsafe { malloc_zone_realloc(zone(), ptr.cast(), Bytes(new_size)) }.cast();
            }
            // SAFETY: the caller guarantees `new_size` at `layout.align()` is
            // a valid layout.
            let resized = unsafe { Layout::from_size_align_unchecked(new_size, layout.align()) };
            // SAFETY: `resized` has a nonzero size.
            let block = unsafe { self.alloc(resized) };
            if !block.is_null() {
                // SAFETY: both blocks are live, distinct and at least the
                // copied length long.
                unsafe {
                    ptr.copy_to_nonoverlapping(block, layout.size().min(new_size));
                }
                // SAFETY: `ptr` is a live block allocated with `layout`.
                unsafe {
                    self.dealloc(ptr, layout);
                }
            }
            block
        }
    }
}

#[cfg(test)]
mod tests
{
    extern crate alloc;

    use alloc::alloc::alloc;
    use alloc::alloc::alloc_zeroed;
    use alloc::alloc::dealloc;
    use alloc::alloc::realloc;
    use core::alloc::Layout;

    /// Every layout the witnesses exercise.
    ///
    /// # Specification
    /// - ensures: yields, for each alignment from 1 to 16 KiB in powers of two
    ///   that straddle `malloc_zone_malloc`'s 16 bytes — 1, 2, 4, 8, 16, 32,
    ///   64, 128, 4 KiB and 16 KiB — three layouts: half the alignment (one
    ///   byte at an alignment of one), the alignment, and three alignments and
    ///   one.
    /// - panics: none.
    /// - executable: none — the layouts are the witnesses' inputs, and every
    ///   assertion reads them back.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the witnesses fail on a layout this omits only if
    ///   another branch fails too; each branch of the allocator is reached by
    ///   several of these layouts.
    /// - witness: `allocator::tests::every_alignment_is_served_aligned`
    /// - witness: `allocator::tests::zeroed_blocks_read_zero_after_reuse`
    /// - witness: `allocator::tests::reallocation_keeps_contents_and_alignment`
    fn layouts() -> impl Iterator<Item = Layout>
    {
        [1, 2, 4, 8, 16, 32, 64, 128, 0x1000, 0x4000]
            .into_iter()
            .flat_map(|align: usize| {
                [
                    align.div_ceil(2),
                    align,
                    align.saturating_mul(3).saturating_add(1),
                ]
                .into_iter()
                .filter_map(move |size| Layout::from_size_align(size, align).ok())
            })
    }

    #[test]
    fn every_alignment_is_served_aligned()
    {
        for layout in layouts() {
            // SAFETY: `layout` has a nonzero size.
            let block = unsafe { alloc(layout) };
            assert!(!block.is_null(), "{layout:?} was refused");
            assert_eq!(
                block.align_offset(layout.align()),
                0,
                "{layout:?} landed at {block:p}"
            );
            // SAFETY: the block holds `layout.size()` writable bytes.
            unsafe {
                block.write_bytes(0xA5, layout.size());
            }
            // SAFETY: the block was allocated with `layout`.
            unsafe {
                dealloc(block, layout);
            }
        }
    }

    #[test]
    fn zeroed_blocks_read_zero_after_reuse()
    {
        for layout in layouts() {
            let dirty: Vec<*mut u8> = core::iter::repeat_with(|| {
                // SAFETY: `layout` has a nonzero size.
                let block = unsafe { alloc(layout) };
                assert!(!block.is_null(), "{layout:?} was refused");
                // SAFETY: the block holds `layout.size()` writable bytes.
                unsafe {
                    block.write_bytes(0xA5, layout.size());
                }
                block
            })
            .take(64)
            .collect();
            for block in dirty {
                // SAFETY: the block was allocated with `layout`.
                unsafe {
                    dealloc(block, layout);
                }
            }
            for _ in 0_usize .. 64 {
                // SAFETY: `layout` has a nonzero size.
                let block = unsafe { alloc_zeroed(layout) };
                assert!(!block.is_null(), "cleared {layout:?} was refused");
                assert_eq!(
                    block.align_offset(layout.align()),
                    0,
                    "cleared {layout:?} landed at {block:p}"
                );
                // SAFETY: the block holds `layout.size()` initialized bytes.
                let bytes = unsafe { core::slice::from_raw_parts(block, layout.size()) };
                assert!(
                    bytes.iter().all(|&byte| byte == 0),
                    "cleared {layout:?} was not zero"
                );
                // SAFETY: the block was allocated with `layout`.
                unsafe {
                    dealloc(block, layout);
                }
            }
        }
    }

    #[test]
    fn reallocation_keeps_contents_and_alignment()
    {
        let pattern = |offset: usize| offset.to_le_bytes()[0];
        for layout in layouts() {
            let size = layout.size();
            // SAFETY: `layout` has a nonzero size.
            let block = unsafe { alloc(layout) };
            assert!(!block.is_null(), "{layout:?} was refused");
            for offset in 0 .. size {
                // SAFETY: `offset` is inside the block.
                unsafe {
                    block.wrapping_add(offset).write(pattern(offset));
                }
            }
            let grown = Layout::from_size_align(size.saturating_mul(5), layout.align()).unwrap();
            // SAFETY: the block was allocated with `layout`, and `grown` is a
            // valid layout of a nonzero size.
            let block = unsafe { realloc(block, layout, grown.size()) };
            assert!(
                !block.is_null(),
                "growing {layout:?} to {grown:?} was refused"
            );
            assert_eq!(
                block.align_offset(grown.align()),
                0,
                "{grown:?} landed at {block:p}"
            );
            // SAFETY: the grown block holds the `size` bytes it kept.
            let kept = unsafe { core::slice::from_raw_parts(block, size) };
            assert!(
                kept.iter().copied().eq((0 .. size).map(pattern)),
                "growing {layout:?} lost its contents"
            );
            let shrunk = Layout::from_size_align(size.div_ceil(2), layout.align()).unwrap();
            // SAFETY: the block was allocated with `grown`, and `shrunk` is a
            // valid layout of a nonzero size.
            let block = unsafe { realloc(block, grown, shrunk.size()) };
            assert!(
                !block.is_null(),
                "shrinking {grown:?} to {shrunk:?} was refused"
            );
            assert_eq!(
                block.align_offset(shrunk.align()),
                0,
                "{shrunk:?} landed at {block:p}"
            );
            // SAFETY: the shrunk block holds the `shrunk.size()` bytes it kept.
            let kept = unsafe { core::slice::from_raw_parts(block, shrunk.size()) };
            assert!(
                kept.iter().copied().eq((0 .. shrunk.size()).map(pattern)),
                "shrinking {grown:?} lost its contents"
            );
            // SAFETY: the block was allocated with `shrunk`.
            unsafe {
                dealloc(block, shrunk);
            }
        }
    }
}
