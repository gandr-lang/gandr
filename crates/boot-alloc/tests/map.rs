//! The mapping calls against the host: the host is the oracle of what it
//! maps, protects and unmaps.

use core::num::NonZeroUsize;

use gandr_boot_alloc::Bytes;
use gandr_boot_alloc::Operation;
use gandr_boot_alloc::PageSize;
use gandr_boot_alloc::Pages;
use gandr_boot_alloc::Protection;
use gandr_boot_alloc::Refused;

use crate::host;

/// The error number of an argument that the call does not take.
const EINVAL: u16 = 22;

/// The error number of a call that finds no memory.
const ENOMEM: u16 = 12;

/// `count` pages.
fn pages(count: usize) -> Pages
{
    Pages(NonZeroUsize::new(count).expect("a count of pages is not zero"))
}

/// The operation and the error number of `refused`.
fn named(refused: Refused) -> (Operation, u16)
{
    (refused.operation(), refused.number().0.get())
}

/// Each page of a readable and writable block takes a byte at its first and
/// its last address, and reads both back. The block is aligned to a page.
#[test]
fn a_block_takes_a_byte_on_each_page()
{
    let page = host::page();
    let size = page.length().0.get();
    let block = gandr_boot_alloc::map(page, pages(16), Protection::ReadWrite)
        .expect("the host maps 16 pages");
    assert_eq!(16 * size, block.length().0.get());
    let base = block.base().0.as_ptr();
    assert_eq!(0, base.addr() % size);
    for (index, mark) in (0 .. 16).zip(1_u8 ..) {
        let first = base.wrapping_add(index * size);
        let last = first.wrapping_add(size - 1);
        // SAFETY: the block holds 16 readable and writable pages.
        unsafe {
            first.write(mark);
        }
        // SAFETY: as above.
        unsafe {
            last.write(mark.wrapping_neg());
        }
    }
    for (index, mark) in (0 .. 16).zip(1_u8 ..) {
        let first = base.wrapping_add(index * size);
        let last = first.wrapping_add(size - 1);
        // SAFETY: as above.
        let (first, last) = (unsafe { first.read() }, unsafe { last.read() });
        assert_eq!((mark, mark.wrapping_neg()), (first, last), "page {index}");
    }
    gandr_boot_alloc::unmap(block).expect("the host unmaps the block");
}

/// A block made read-only reads the byte that it held, and the same block
/// made writable again takes a new byte.
#[test]
fn a_block_made_read_only_reads_its_byte()
{
    let page = host::page();
    let block =
        gandr_boot_alloc::map(page, pages(1), Protection::ReadWrite).expect("the host maps a page");
    let base = block.base().0.as_ptr();
    // SAFETY: the page is readable and writable.
    unsafe {
        base.write(0xA5);
    }
    gandr_boot_alloc::protect(&block, Protection::Read).expect("the host makes the page read-only");
    // SAFETY: the page is readable.
    assert_eq!(0xA5, unsafe { base.read() });
    gandr_boot_alloc::protect(&block, Protection::ReadWrite)
        .expect("the host makes the page writable");
    // SAFETY: the page is readable and writable.
    unsafe {
        base.write(0x5A);
    }
    // SAFETY: as above.
    assert_eq!(0x5A, unsafe { base.read() });
    gandr_boot_alloc::unmap(block).expect("the host unmaps the block");
}

/// A count of pages whose bytes overflow a word is refused under the name
/// `map` with `ENOMEM` before the host sees it. A count past the address
/// space is refused by the host under the same name and number. A block
/// that stands keeps its byte through both.
#[test]
fn a_count_past_the_address_space_is_refused()
{
    let page = host::page();
    let block =
        gandr_boot_alloc::map(page, pages(1), Protection::ReadWrite).expect("the host maps a page");
    let base = block.base().0.as_ptr();
    // SAFETY: the page is readable and writable.
    unsafe {
        base.write(0x3C);
    }
    let overflow = gandr_boot_alloc::map(page, pages(usize::MAX), Protection::ReadWrite);
    assert_eq!(Some((Operation::Map, ENOMEM)), overflow.err().map(named));
    let count = (1_usize << 60_u32) >> page.length().0.trailing_zeros();
    let past = gandr_boot_alloc::map(page, pages(count), Protection::ReadWrite);
    assert_eq!(Some((Operation::Map, ENOMEM)), past.err().map(named));
    // SAFETY: the page is readable.
    assert_eq!(0x3C, unsafe { base.read() });
    gandr_boot_alloc::unmap(block).expect("the host unmaps the block");
}

/// A page size is a power of two: 0, 3 and one byte past the host's page are
/// refused under the name `page` with `EINVAL`, and the host's page is
/// admitted.
#[test]
fn a_page_size_is_a_power_of_two()
{
    let host = host::page().length().0.get();
    for bytes in [0, 3, host + 1] {
        assert_eq!(
            Some((Operation::Page, EINVAL)),
            PageSize::new(Bytes(bytes)).err().map(named),
            "{bytes}"
        );
    }
    assert_eq!(
        Ok(host),
        PageSize::new(Bytes(host)).map(|page| page.length().0.get())
    );
}
