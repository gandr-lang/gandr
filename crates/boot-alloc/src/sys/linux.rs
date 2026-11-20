//! The three mapping calls on Linux, each a system call by the crate's own
//! function in assembly. No libc stands between the crate and the kernel.

use core::num::NonZeroU16;
use core::ptr::NonNull;

use crate::Backing;
use crate::Base;
use crate::ENOMEM;
use crate::ErrorNumber;
use crate::Length;
use crate::Protection;
use crate::Request;

#[cfg(target_arch = "aarch64")]
mod aarch64;
#[cfg(target_arch = "riscv64")]
mod riscv64;
#[cfg(target_arch = "x86_64")]
mod x86_64;

#[cfg(target_arch = "aarch64")]
use aarch64 as arch;
#[cfg(target_arch = "riscv64")]
use riscv64 as arch;
#[cfg(target_arch = "x86_64")]
use x86_64 as arch;

/// The number of a system call.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Call(usize);

/// One register's word, as the kernel reads it or answers it.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Raw(usize);

/// The flag of a mapping that no file backs.
const MAP_ANONYMOUS: usize = 0x20;

/// The flag of a mapping that no other process sees.
const MAP_PRIVATE: usize = 0x02;

/// The flag of a mapping whose pages the kernel counts only as they are
/// touched.
const MAP_NORESERVE: usize = 0x4000;

/// The largest error number: the kernel answers an error `e` as `-e`, from
/// `-4095` to `-1`.
const LAST_ERROR: u16 = 4095;

/// The kernel's answer `raw` as a word or as its error number.
///
/// # Specification
/// - ensures: an answer from `-4095` to `-1` is the error number of its
///   negation; each other answer is the word itself.
/// - panics: none.
/// - executable: none — the answers come from the kernel.
///
/// # Adequacy
/// - hypothesis: L3 — a map past the address space refuses with `ENOMEM`, and a
///   page that `map` gives takes a byte.
/// - witness: `tests::map::a_count_past_the_address_space_is_refused`
fn answer(raw: Raw) -> Result<Raw, ErrorNumber>
{
    match u16::try_from(raw.0.wrapping_neg())
        .ok()
        .and_then(NonZeroU16::new)
    {
        Some(number) if number.get() <= LAST_ERROR => Err(ErrorNumber(number)),
        _ => Ok(raw),
    }
}

/// Maps `length` bytes of private anonymous memory as `request` asks, at an
/// address that the kernel picks. An unreserved block takes
/// `MAP_NORESERVE`.
///
/// # Specification
/// - ensures: the base of the new mapping, or the kernel's error number.
/// - panics: none.
/// - executable: none — the kernel decides what it maps.
///
/// # Adequacy
/// - hypothesis: L3 — each page of a reserved and of an unreserved mapping
///   takes a byte.
/// - witness: `tests::map::a_block_takes_a_byte_on_each_page`
pub fn map(
    length: Length,
    request: Request,
) -> Result<Base, ErrorNumber>
{
    let flags = match request.backing {
        Backing::Reserved => MAP_PRIVATE | MAP_ANONYMOUS,
        Backing::Unreserved => MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE,
    };
    // SAFETY: a private anonymous mapping at an address that the kernel picks
    // touches no memory that the process holds.
    let raw = unsafe {
        arch::syscall6(arch::MMAP, [
            Raw(0),
            Raw(length.0.get()),
            Raw(usize::from(super::bits(request.protection).0)),
            Raw(flags),
            Raw(usize::MAX),
            Raw(0),
        ])
    };
    let base = answer(raw)?;
    // The kernel makes the mapping outside the abstract machine, so its base
    // takes the exposed provenance.
    let pointer = core::ptr::with_exposed_provenance_mut::<u8>(base.0);
    if let Some(base) = NonNull::new(pointer) {
        return Ok(Base(base));
    }
    // The kernel gives the address 0 only on a host whose `vm.mmap_min_addr`
    // is 0. A block holds no null base, so the crate gives the mapping back
    // and refuses.
    // SAFETY: the mapping is the call's own, and nothing reads it.
    let _unmapped = unsafe {
        arch::syscall6(arch::MUNMAP, [
            Raw(0),
            Raw(length.0.get()),
            Raw(0),
            Raw(0),
            Raw(0),
            Raw(0),
        ])
    };
    Err(ENOMEM)
}

/// Sets the protection of the `length` bytes at `base` to `protection`.
///
/// # Safety
///
/// - unsafe invariants: no reference into the bytes lives that the new
///   protection forbids.
///
/// # Specification
/// - ensures: the kernel's error number when it refuses.
/// - panics: none.
/// - executable: none — the kernel sets the protection.
///
/// # Adequacy
/// - hypothesis: L3 — a page made read-only reads its byte, and a page made
///   writable again takes one.
/// - witness: `tests::map::a_block_made_read_only_reads_its_byte`
pub unsafe fn protect(
    base: Base,
    length: Length,
    protection: Protection,
) -> Result<(), ErrorNumber>
{
    // SAFETY: the caller's invariants hold for the bytes.
    let raw = unsafe {
        arch::syscall6(arch::MPROTECT, [
            Raw(base.0.as_ptr().addr()),
            Raw(length.0.get()),
            Raw(usize::from(super::bits(protection).0)),
            Raw(0),
            Raw(0),
            Raw(0),
        ])
    };
    answer(raw).map(|_| ())
}

/// Unmaps the `length` bytes at `base`.
///
/// # Safety
///
/// - unsafe invariants: no reference into the bytes lives.
///
/// # Specification
/// - ensures: the kernel's error number when it refuses.
/// - panics: none.
/// - executable: none — the kernel unmaps the bytes.
///
/// # Adequacy
/// - hypothesis: L3 — the mapped pages of the process are as many after a heap
///   ends as before it started.
/// - witness: `pages::heap::mixed_blocks_leave_the_mapped_pages_as_they_were`
pub unsafe fn unmap(
    base: Base,
    length: Length,
) -> Result<(), ErrorNumber>
{
    // SAFETY: the caller's invariants hold for the bytes.
    let raw = unsafe {
        arch::syscall6(arch::MUNMAP, [
            Raw(base.0.as_ptr().addr()),
            Raw(length.0.get()),
            Raw(0),
            Raw(0),
            Raw(0),
            Raw(0),
        ])
    };
    answer(raw).map(|_| ())
}
