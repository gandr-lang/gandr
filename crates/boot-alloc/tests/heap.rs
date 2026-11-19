//! The heap against its contract: each live block keeps its bytes, has its
//! alignment, and grows in place within its size.

use core::alloc::Layout;

use gandr_boot_alloc::Base;
use gandr_boot_alloc::Heap;
use gandr_boot_alloc::Operation;

use crate::host;

/// A live block: its address, its layout and the byte that fills it.
struct Live
{
    /// The block's first byte.
    base: Base,
    /// The layout that the block was given for.
    layout: Layout,
    /// The byte in each of its first `layout.size()` bytes.
    mark: u8,
}

/// Fills the first `layout.size()` bytes at `base` with `mark`.
fn fill(
    base: Base,
    layout: Layout,
    mark: u8,
)
{
    // SAFETY: the block holds at least `layout.size()` writable bytes.
    unsafe {
        base.0.as_ptr().write_bytes(mark, layout.size());
    }
}

/// Whether each of the first `layout.size()` bytes of `live` is its mark.
fn holds(live: &Live) -> bool
{
    // SAFETY: the block holds at least `layout.size()` readable bytes.
    let bytes = unsafe { core::slice::from_raw_parts(live.base.0.as_ptr(), live.layout.size()) };
    bytes.iter().all(|&byte| byte == live.mark)
}

/// Blocks of each class and of whole pages, with alignments from 1 to a
/// page, keep their bytes while blocks around them are freed and taken
/// again. Each block has its alignment. An alignment past a page is refused
/// under the name `allocate` with `EINVAL`.
#[test]
fn each_block_keeps_its_bytes_and_its_alignment()
{
    let page = host::page();
    let heap = Heap::new(page);
    let mut live = Vec::new();
    let mut seed = 0x9E37_79B9_u32;
    for (index, mark) in (0 .. 3000_usize).zip((1_u8 ..= 255).cycle()) {
        seed ^= seed << 13_u32;
        seed ^= seed >> 17_u32;
        seed ^= seed << 5_u32;
        let size = usize::try_from(seed % 9000).expect("a size fits a word");
        let align = 1 << ((seed >> 24_u32) % (page.length().0.trailing_zeros() + 1));
        let layout = Layout::from_size_align(size, align).expect("a layout");
        let block = heap
            .allocate(layout)
            .expect("the heap gives a block")
            .base();
        assert_eq!(
            0,
            block.0.as_ptr().addr() % align,
            "block {index}: {layout:?}"
        );
        fill(block, layout, mark);
        live.push(Live {
            base: block,
            layout,
            mark,
        });
        if index % 3 == 2 {
            let gone =
                live.swap_remove(usize::try_from(seed).expect("a seed fits a word") % live.len());
            // SAFETY: the heap gave the block for its layout, and the test
            // keeps no reference into it.
            unsafe { heap.free(gone.base, gone.layout) }.expect("the heap takes the block back");
        }
    }
    for (index, block) in live.iter().enumerate() {
        assert!(holds(block), "block {index}: {:?}", block.layout);
    }
    let past = Layout::from_size_align(8192, page.length().0.get() * 2).expect("a layout");
    let refused = heap
        .allocate(past)
        .err()
        .map(|refused| (refused.operation(), refused.number().0.get()));
    assert_eq!(Some((Operation::Allocate, 22)), refused);
    for block in live {
        // SAFETY: as above.
        unsafe { heap.free(block.base, block.layout) }.expect("the heap takes the block back");
    }
}

/// A block that grows within its class or its pages keeps its address. A
/// block that grows past them moves, and it keeps its first bytes.
#[test]
fn a_grown_block_keeps_its_bytes()
{
    let page = host::page().length().0.get();
    let heap = Heap::new(host::page());
    let layout = |size| Layout::from_size_align(size, 8).expect("a layout");
    let first = heap
        .allocate(layout(24))
        .expect("the heap gives a block")
        .base();
    fill(first, layout(24), 7);
    // SAFETY: the heap gave the block for 24 bytes, and the test keeps no
    // reference into it.
    let within = unsafe { heap.grow(first, layout(24), layout(30)) }
        .expect("the block grows")
        .base();
    assert_eq!(first, within);
    // SAFETY: as above, for 30 bytes.
    let moved = unsafe { heap.grow(within, layout(30), layout(100)) }
        .expect("the block grows")
        .base();
    assert_ne!(within, moved);
    assert!(holds(&Live {
        base: moved,
        layout: layout(24),
        mark: 7
    }));
    fill(moved, layout(100), 9);
    // SAFETY: as above, for 100 bytes.
    let paged = unsafe { heap.grow(moved, layout(100), layout(page + 1)) }
        .expect("the block grows")
        .base();
    assert!(holds(&Live {
        base: paged,
        layout: layout(100),
        mark: 9
    }));
    // SAFETY: as above, for one byte past a page.
    let same = unsafe { heap.grow(paged, layout(page + 1), layout(2 * page)) }
        .expect("the block grows")
        .base();
    assert_eq!(paged, same);
    // SAFETY: as above, for two pages.
    unsafe { heap.free(same, layout(2 * page)) }.expect("the heap takes the block back");
}

/// A vector whose allocator is a shared reference to the heap grows to
/// 10000 words and reads each one back.
#[test]
fn a_vector_grows_in_the_heap()
{
    let heap = Heap::new(host::page());
    let mut words = Vec::new_in(&heap);
    for word in 0 .. 10_000_u64 {
        words.push(word.wrapping_mul(0x9E37_79B9_7F4A_7C15));
    }
    for (word, &held) in (0 .. 10_000_u64).zip(&words) {
        assert_eq!(word.wrapping_mul(0x9E37_79B9_7F4A_7C15), held);
    }
}
