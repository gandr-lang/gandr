//! The mapping calls against the host: the host is the oracle of what it
//! maps, protects and unmaps.

use core::num::NonZeroU16;
use core::num::NonZeroUsize;

use gandr_boot_alloc::Backing;
#[cfg(target_os = "linux")]
use gandr_boot_alloc::Block;
use gandr_boot_alloc::Bytes;
use gandr_boot_alloc::ErrorNumber;
use gandr_boot_alloc::Mapper;
use gandr_boot_alloc::Operation;
use gandr_boot_alloc::PageSize;
use gandr_boot_alloc::Pages;
use gandr_boot_alloc::Protection;
use gandr_boot_alloc::Refused;
use gandr_boot_alloc::Request;

use crate::host;

/// The error number of an argument that the call does not take.
const EINVAL: ErrorNumber = ErrorNumber(NonZeroU16::new(22).expect("22 is not zero"));

/// The error number of a call that finds no memory.
const ENOMEM: ErrorNumber = ErrorNumber(NonZeroU16::new(12).expect("12 is not zero"));

/// The request of readable and writable pages for which the host reserves
/// memory.
const READ_WRITE: Request = Request {
    protection: Protection::ReadWrite,
    backing: Backing::Reserved,
};

/// A count of pages that a test asks for.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Count(usize);

/// A mapper over the host's pages.
///
/// # Specification
/// trivial.
fn mapper() -> Mapper
{
    Mapper::new(host::page())
}

/// `count` pages.
///
/// # Specification
/// trivial.
fn pages(count: Count) -> Pages
{
    Pages(NonZeroUsize::new(count.0).expect("a count of pages is not zero"))
}

/// The operation and the error number of `refused`.
///
/// # Specification
/// trivial.
fn named(refused: Refused) -> (Operation, ErrorNumber)
{
    (refused.operation(), refused.number())
}

/// The flags that the kernel's map of the process shows for the mapping that
/// holds the base of `block`, from `/proc/self/smaps`.
///
/// # Specification
/// trivial.
#[cfg(target_os = "linux")]
fn kernel_flags(block: &Block) -> Vec<String>
{
    let address = block.base().0.as_ptr().addr();
    let smaps = std::fs::read_to_string("/proc/self/smaps").expect("the kernel gives smaps");
    let mut inside = false;
    for line in smaps.lines() {
        let range = line
            .split_once(' ')
            .and_then(|(range, _)| range.split_once('-'))
            .and_then(|(start, end)| {
                Some((
                    usize::from_str_radix(start, 16).ok()?,
                    usize::from_str_radix(end, 16).ok()?,
                ))
            });
        if let Some((start, end)) = range {
            inside = (start .. end).contains(&address);
        }
        else if let Some(flags) = line.strip_prefix("VmFlags:").filter(|_| inside) {
            return flags.split_whitespace().map(str::to_owned).collect();
        }
    }
    panic!("smaps holds the mapping at {address:#x}");
}

/// Each page of a readable and writable block takes a byte at its first and
/// its last address, and reads both back, for a reserved block and for an
/// unreserved one. The block is aligned to a page.
#[test]
fn a_block_takes_a_byte_on_each_page()
{
    let mapper = mapper();
    let size = mapper.page().length().0.get();
    for backing in [Backing::Reserved, Backing::Unreserved] {
        let request = Request {
            protection: Protection::ReadWrite,
            backing,
        };
        let block = mapper
            .map(pages(Count(16)), request)
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
            assert_eq!(
                (mark, mark.wrapping_neg()),
                (first, last),
                "{backing:?} page {index}"
            );
        }
        block.unmap().expect("the host unmaps the block");
    }
}

/// On Linux the host reserves memory for a reserved block alone. The
/// kernel's map of the process shows the flag `nr` on an unreserved block,
/// and no such flag on a reserved one.
#[cfg(target_os = "linux")]
#[test]
fn the_host_reserves_memory_for_a_reserved_block_alone()
{
    let mapper = mapper();
    for (backing, unreserved) in [(Backing::Reserved, false), (Backing::Unreserved, true)] {
        let request = Request {
            protection: Protection::ReadWrite,
            backing,
        };
        let block = mapper
            .map(pages(Count(4)), request)
            .expect("the host maps 4 pages");
        let flags = kernel_flags(&block);
        assert_eq!(
            unreserved,
            flags.iter().any(|flag| flag == "nr"),
            "{backing:?}: {flags:?}"
        );
        block.unmap().expect("the host unmaps the block");
    }
}

/// A block made read-only reads the byte that it held, and the same block
/// made writable again takes a new byte.
#[test]
fn a_block_made_read_only_reads_its_byte()
{
    let block = mapper()
        .map(pages(Count(1)), READ_WRITE)
        .expect("the host maps a page");
    let base = block.base().0.as_ptr();
    // SAFETY: the page is readable and writable.
    unsafe {
        base.write(0xA5);
    }
    block
        .protect(Protection::Read)
        .expect("the host makes the page read-only");
    // SAFETY: the page is readable.
    assert_eq!(0xA5, unsafe { base.read() });
    block
        .protect(Protection::ReadWrite)
        .expect("the host makes the page writable");
    // SAFETY: the page is readable and writable.
    unsafe {
        base.write(0x5A);
    }
    // SAFETY: as above.
    assert_eq!(0x5A, unsafe { base.read() });
    block.unmap().expect("the host unmaps the block");
}

/// A count of pages whose bytes overflow a word is refused under the name
/// `map` with `ENOMEM` before the host sees it. A count past the address
/// space is refused by the host under the same name and number. A block
/// that stands keeps its byte through both.
#[test]
fn a_count_past_the_address_space_is_refused()
{
    let mapper = mapper();
    let block = mapper
        .map(pages(Count(1)), READ_WRITE)
        .expect("the host maps a page");
    let base = block.base().0.as_ptr();
    // SAFETY: the page is readable and writable.
    unsafe {
        base.write(0x3C);
    }
    let overflow = mapper.map(pages(Count(usize::MAX)), READ_WRITE);
    assert_eq!(Some((Operation::Map, ENOMEM)), overflow.err().map(named));
    let count = (1_usize << 60_u32) >> mapper.page().length().0.trailing_zeros();
    let past = mapper.map(pages(Count(count)), READ_WRITE);
    assert_eq!(Some((Operation::Map, ENOMEM)), past.err().map(named));
    // SAFETY: the page is readable.
    assert_eq!(0x3C, unsafe { base.read() });
    block.unmap().expect("the host unmaps the block");
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
