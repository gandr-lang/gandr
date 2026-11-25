//! The four file calls on Linux, each a system call by the crate's own
//! function in assembly. No libc stands between the crate and the kernel.

use core::num::NonZeroU16;

use gandr_boot_core::Length;
use gandr_boot_core::Place;
use gandr_boot_core::Range;

use crate::Descriptor;
use crate::ErrorNumber;

#[cfg(target_arch = "riscv64")]
mod riscv64;
#[cfg(target_arch = "x86_64")]
mod x86_64;

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
pub struct Raw(pub usize);

/// The directory that `openat` reads a relative path from: the working
/// directory of the process, `AT_FDCWD`.
const AT_FDCWD: isize = -100;

/// The flag of a descriptor that only reads.
const O_RDONLY: usize = 0;

/// The flag of a descriptor that the kernel closes when the process runs
/// another program.
const O_CLOEXEC: usize = 0o2_000_000;

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
/// - hypothesis: L3 — a path with no file refuses with `ENOENT`, a closed
///   descriptor refuses with `EBADF`, and a read gives its count.
/// - witness: `tests::file::a_path_with_no_file_is_refused_with_the_error_number_of_the_kernel`
/// - witness: `tests::file::a_closed_descriptor_is_refused_with_ebadf`
pub fn answer(raw: Raw) -> Result<Raw, ErrorNumber>
{
    match u16::try_from(raw.0.wrapping_neg())
        .ok()
        .and_then(NonZeroU16::new)
    {
        Some(number) if number.get() <= LAST_ERROR => Err(ErrorNumber(number)),
        _ => Ok(raw),
    }
}

/// The word of `descriptor`, as the kernel reads an `unsigned int`.
///
/// # Specification
/// trivial.
fn descriptor_word(descriptor: Descriptor) -> Raw
{
    Raw(usize::try_from(descriptor.0.cast_unsigned()).unwrap_or(usize::MAX))
}

/// Opens the file at `path`, relative to the working directory, to read it.
///
/// # Safety
///
/// - unsafe invariants: the bytes of `path` are readable, and a zero byte
///   follows its last byte.
///
/// # Specification
/// - ensures: the descriptor that the kernel gives, or its error number.
/// - panics: none.
/// - executable: none — the kernel opens the file.
///
/// # Adequacy
/// - hypothesis: L3 — a file of the tree opens, and a path with no file is
///   refused with `ENOENT`.
/// - witness: `tests::file::a_path_with_no_file_is_refused_with_the_error_number_of_the_kernel`
pub unsafe fn open(path: Range) -> Result<Descriptor, ErrorNumber>
{
    // SAFETY: the caller's invariants hold for the path and its zero byte, and
    // the call writes no memory of the process.
    let raw = unsafe {
        arch::syscall4(arch::OPENAT, [
            Raw(AT_FDCWD.cast_unsigned()),
            Raw(path.base.addr()),
            Raw(O_RDONLY | O_CLOEXEC),
            Raw(0),
        ])
    };
    let descriptor = answer(raw)?;
    // The kernel gives a descriptor from 0 to `i32::MAX`, so the word fits.
    Ok(Descriptor(i32::try_from(descriptor.0).unwrap_or(i32::MAX)))
}

/// Reads at most `place.length` bytes of `descriptor` into `place`.
///
/// # Safety
///
/// - unsafe invariants: the bytes of `place` are writable where it is not
///   empty.
///
/// # Specification
/// - ensures: the count that the kernel wrote, or its error number.
/// - panics: none.
/// - executable: none — the kernel writes the bytes.
///
/// # Adequacy
/// - hypothesis: L3 — a file of the tree reads whole in steps of one page.
/// - witness: `tests::file::a_file_of_the_tree_reads_whole_in_steps_of_one_page`
pub unsafe fn read(
    descriptor: Descriptor,
    place: Place,
) -> Result<Length, ErrorNumber>
{
    // SAFETY: the caller's invariants hold for the bytes of the place, which
    // is all that the call writes.
    let raw = unsafe {
        arch::syscall4(arch::READ, [
            descriptor_word(descriptor),
            Raw(place.base.addr()),
            Raw(place.length.0),
            Raw(0),
        ])
    };
    answer(raw).map(|count| Length(count.0))
}

/// Gives at most `bytes.length` bytes of `bytes` to `descriptor`.
///
/// # Safety
///
/// - unsafe invariants: the bytes of `bytes` are readable where it is not
///   empty.
///
/// # Specification
/// - ensures: the count that the kernel took, or its error number.
/// - panics: none.
/// - executable: none — the kernel takes the bytes.
///
/// # Adequacy
/// - hypothesis: L3 — the bytes of a write reach the other end of a socket, and
///   a socket that cannot take each byte gives a short count.
/// - witness: `tests::write::a_write_gives_each_byte_to_the_other_end`
/// - witness: `tests::write::a_full_socket_takes_a_short_write_of_the_first_bytes`
pub unsafe fn write(
    descriptor: Descriptor,
    bytes: Range,
) -> Result<Length, ErrorNumber>
{
    // SAFETY: the caller's invariants hold for the bytes of the range, and the
    // call writes no memory of the process.
    let raw = unsafe {
        arch::syscall4(arch::WRITE, [
            descriptor_word(descriptor),
            Raw(bytes.base.addr()),
            Raw(bytes.length.0),
            Raw(0),
        ])
    };
    answer(raw).map(|count| Length(count.0))
}

/// Closes `descriptor`.
///
/// # Specification
/// - ensures: the kernel's error number when it refuses.
/// - panics: none.
/// - executable: none — the kernel closes the descriptor.
///
/// # Adequacy
/// - hypothesis: L3 — a second close of one descriptor is refused with `EBADF`.
/// - witness: `tests::file::a_closed_descriptor_is_refused_with_ebadf`
pub fn close(descriptor: Descriptor) -> Result<(), ErrorNumber>
{
    // SAFETY: a close writes no memory of the process. A descriptor that the
    // process does not hold is refused with `EBADF`.
    let raw = unsafe {
        arch::syscall4(arch::CLOSE, [
            descriptor_word(descriptor),
            Raw(0),
            Raw(0),
            Raw(0),
        ])
    };
    answer(raw).map(|_| ())
}
