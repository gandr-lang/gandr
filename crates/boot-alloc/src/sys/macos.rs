//! The three mapping calls on macOS, each a declared function of the system
//! library. The kernel of macOS keeps no stable numbers for its calls, so
//! the system library is its interface.

use core::ffi::c_int;
use core::ffi::c_void;
use core::num::NonZeroU16;
use core::ptr::NonNull;

use crate::Base;
use crate::ENOMEM;
use crate::ErrorNumber;
use crate::Length;
use crate::Protection;
use crate::Request;

/// A C `int` of the system library: a protection, the flags, a descriptor or
/// an answer.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Int(c_int);

/// A C `size_t` of the system library: the bytes of a mapping.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Size(usize);

/// A C `off_t` of the system library: an offset into a file.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct FileOffset(i64);

/// The mapping calls that libSystem declares in `<sys/mman.h>`, and the
/// thread's error number of `<errno.h>`.
///
/// # Safety
///
/// - unsafe invariants: each signature matches the declaration, with
///   transparent wrappers of `size_t`, `int` and `off_t`; a call names a range
///   of its own mapping, or a range that the kernel picks.
#[link(name = "System")]
#[expect(
    unused_doc_comments,
    reason = "the policy lint reads this block's safety section; rustdoc renders none on an extern block"
)]
unsafe extern "C" {
    /// The system library's `mmap`.
    ///
    /// # Specification
    /// trivial.
    fn mmap(
        address: *mut c_void,
        length: Size,
        protection: Int,
        flags: Int,
        descriptor: Int,
        offset: FileOffset,
    ) -> *mut c_void;

    /// The system library's `mprotect`.
    ///
    /// # Specification
    /// trivial.
    fn mprotect(
        address: *mut c_void,
        length: Size,
        protection: Int,
    ) -> Int;

    /// The system library's `munmap`.
    ///
    /// # Specification
    /// trivial.
    fn munmap(
        address: *mut c_void,
        length: Size,
    ) -> Int;

    /// The address of the calling thread's error number.
    ///
    /// # Specification
    /// trivial.
    fn __error() -> *mut Int;
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
    // SAFETY: the call reads no argument and writes no memory.
    let address = unsafe { __error() };
    // SAFETY: the system library gives each thread its own error number, and
    // the address stays valid while the thread lives.
    let number = unsafe { address.read() };
    u16::try_from(number.0)
        .ok()
        .and_then(NonZeroU16::new)
        .map_or(ENOMEM, ErrorNumber)
}

/// The protection `protection` as the system library reads it.
///
/// # Specification
/// trivial.
fn protection(protection: Protection) -> Int
{
    Int(c_int::from(super::bits(protection).0))
}

/// Maps `length` bytes of private anonymous memory as `request` asks, at an
/// address that the kernel picks. macOS counts no page before its first
/// touch, so a reserved and an unreserved block take the same flags.
///
/// # Specification
/// - ensures: the base of the new mapping, or the error number of the system
///   library.
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
    // SAFETY: a private anonymous mapping at an address that the kernel picks
    // touches no memory that the process holds.
    let base = unsafe {
        mmap(
            core::ptr::null_mut(),
            Size(length.0.get()),
            self::protection(request.protection),
            Int(MAP_PRIVATE | MAP_ANON),
            Int(-1),
            FileOffset(0),
        )
    };
    // `MAP_FAILED` is the address of all ones.
    if base.addr() == usize::MAX {
        return Err(error());
    }
    // macOS keeps the first page of each process unmapped, so the base of a
    // mapping is never null.
    NonNull::new(base.cast::<u8>()).map(Base).ok_or(ENOMEM)
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
    base: Base,
    length: Length,
    protection: Protection,
) -> Result<(), ErrorNumber>
{
    // SAFETY: the caller's invariants hold for the bytes.
    let answer = unsafe {
        mprotect(
            base.0.as_ptr().cast(),
            Size(length.0.get()),
            self::protection(protection),
        )
    };
    if answer == Int(0) {
        Ok(())
    }
    else {
        Err(error())
    }
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
    base: Base,
    length: Length,
) -> Result<(), ErrorNumber>
{
    // SAFETY: the caller's invariants hold for the bytes.
    let answer = unsafe { munmap(base.0.as_ptr().cast(), Size(length.0.get())) };
    if answer == Int(0) {
        Ok(())
    }
    else {
        Err(error())
    }
}
