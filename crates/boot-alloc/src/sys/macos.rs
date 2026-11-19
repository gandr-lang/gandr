//! The three mapping calls on macOS, each a declared function of the system
//! library. The kernel of macOS keeps no stable numbers for its calls, so
//! the system library is its interface.

use core::ffi::c_int;
use core::ffi::c_void;
use core::num::NonZeroU16;
use core::num::NonZeroUsize;
use core::ptr::NonNull;

use crate::ENOMEM;
use crate::ErrorNumber;
use crate::Protection;

#[link(name = "System")]
unsafe extern "C" {
    /// The system library's `mmap`.
    fn mmap(
        address: *mut c_void,
        length: usize,
        protection: c_int,
        flags: c_int,
        descriptor: c_int,
        offset: i64,
    ) -> *mut c_void;

    /// The system library's `mprotect`.
    fn mprotect(
        address: *mut c_void,
        length: usize,
        protection: c_int,
    ) -> c_int;

    /// The system library's `munmap`.
    fn munmap(
        address: *mut c_void,
        length: usize,
    ) -> c_int;

    /// The address of the calling thread's error number.
    fn __error() -> *mut c_int;
}

/// The flag of a mapping that no file backs.
const MAP_ANON: c_int = 0x1000;

/// The flag of a mapping that no other process sees.
const MAP_PRIVATE: c_int = 0x02;

/// The calling thread's error number, after a call that failed.
///
/// # Specification
/// - ensures: the error number that the system library set, or `ENOMEM` when it
///   set none that a nonzero 16-bit number holds.
/// - panics: none.
/// - executable: none — the system library sets the number.
///
/// # Adequacy
/// - hypothesis: L3 — a map past the address space refuses with `ENOMEM`.
/// - witness: `tests::map::a_count_past_the_address_space_is_refused`
fn error() -> ErrorNumber
{
    // SAFETY: the system library gives each thread its own error number, and
    // the address stays valid while the thread lives.
    let number = unsafe { *__error() };
    ErrorNumber(
        u16::try_from(number)
            .ok()
            .and_then(NonZeroU16::new)
            .unwrap_or(ENOMEM),
    )
}

/// Maps `length` bytes of private anonymous memory with the protection
/// `protection`, at an address that the kernel picks.
///
/// # Specification
/// - ensures: the base of the new mapping, or the error number of the system
///   library.
/// - panics: none.
/// - executable: none — the kernel decides what it maps.
///
/// # Adequacy
/// - hypothesis: L3 — each page of the mapping takes a byte.
/// - witness: `tests::map::a_block_takes_a_byte_on_each_page`
pub fn map(
    length: NonZeroUsize,
    protection: Protection,
) -> Result<NonNull<u8>, ErrorNumber>
{
    // SAFETY: a private anonymous mapping at an address that the kernel picks
    // touches no memory that the process holds.
    let base = unsafe {
        mmap(
            core::ptr::null_mut(),
            length.get(),
            c_int::from(super::bits(protection)),
            MAP_PRIVATE | MAP_ANON,
            -1,
            0,
        )
    };
    // `MAP_FAILED` is the address of all ones.
    if base.addr() == usize::MAX {
        return Err(error());
    }
    // macOS keeps the first page of each process unmapped, so the base of a
    // mapping is never null.
    NonNull::new(base.cast::<u8>()).ok_or(ErrorNumber(ENOMEM))
}

/// Sets the protection of the `length` bytes at `base` to `protection`.
///
/// # Safety
///
/// - unsafe invariants: no reference into the bytes lives that the new
///   protection forbids.
///
/// # Specification
/// - ensures: the error number of the system library when it refuses.
/// - panics: none.
/// - executable: none — the kernel sets the protection.
///
/// # Adequacy
/// - hypothesis: L3 — a page made read-only reads its byte, and a page made
///   writable again takes one.
/// - witness: `tests::map::a_block_made_read_only_reads_its_byte`
pub unsafe fn protect(
    base: NonNull<u8>,
    length: NonZeroUsize,
    protection: Protection,
) -> Result<(), ErrorNumber>
{
    // SAFETY: the caller's invariants hold for the bytes.
    let answer = unsafe {
        mprotect(
            base.as_ptr().cast(),
            length.get(),
            c_int::from(super::bits(protection)),
        )
    };
    if answer == 0 { Ok(()) } else { Err(error()) }
}

/// Unmaps the `length` bytes at `base`.
///
/// # Safety
///
/// - unsafe invariants: no reference into the bytes lives.
///
/// # Specification
/// - ensures: the error number of the system library when it refuses.
/// - panics: none.
/// - executable: none — the kernel unmaps the bytes.
///
/// # Adequacy
/// - hypothesis: L3 — the mapped pages of the process are as many after a heap
///   ends as before it started.
/// - witness: `pages::heap::mixed_blocks_leave_the_mapped_pages_as_they_were`
pub unsafe fn unmap(
    base: NonNull<u8>,
    length: NonZeroUsize,
) -> Result<(), ErrorNumber>
{
    // SAFETY: the caller's invariants hold for the bytes.
    let answer = unsafe { munmap(base.as_ptr().cast(), length.get()) };
    if answer == 0 { Ok(()) } else { Err(error()) }
}
