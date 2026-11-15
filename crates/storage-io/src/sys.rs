//! The system calls that the ring issues: each by the architecture's own
//! instruction, with no C library. The numbers come from the generated
//! table in `uapi`.
//!
//! Each argument goes into a register of its own type ([`registers`]), so a
//! call cannot put an argument in another's place, and a pointer keeps its
//! provenance through the call.

mod registers;

/// The instruction of the architecture that the crate builds for.
#[cfg_attr(target_arch = "aarch64", path = "sys/arch/aarch64.rs")]
#[cfg_attr(target_arch = "riscv64", path = "sys/arch/riscv64.rs")]
#[cfg_attr(target_arch = "x86_64", path = "sys/arch/x86_64.rs")]
mod arch;

use core::ffi::c_void;
use core::ptr::NonNull;
use std::os::fd::BorrowedFd;
use std::os::fd::FromRawFd as _;
use std::os::fd::OwnedFd;

use crate::sys::registers::Argument;
use crate::sys::registers::Number;
use crate::uapi;
use crate::uapi::io_uring_params;
use crate::uapi::syscall;

/// One machine word that a system call takes or answers.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Word(usize);

impl From<usize> for Word
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}

impl From<Word> for usize
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(word: Word) -> Self
    {
        word.0
    }
}

impl From<u32> for Word
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: u32) -> Self
    {
        Self(usize::try_from(value).unwrap_or(usize::MAX))
    }
}

impl Word
{
    /// The sum of two words, which saturates at the largest word.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn plus(
        self,
        other: Self,
    ) -> Self
    {
        Self(self.0.saturating_add(other.0))
    }

    /// The product of two words, which saturates at the largest word.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn times(
        self,
        other: Self,
    ) -> Self
    {
        Self(self.0.saturating_mul(other.0))
    }
}

/// An error number that the kernel answers, as `errno(3)` names it.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Errno(u16);

impl Errno
{
    /// The caller may not use the ring: a container's policy, or a kernel
    /// switch.
    pub const PERMISSION: Self = Self(1);
    /// No such entry: a cancel found no submission of its key.
    pub const NO_ENTRY: Self = Self(2);
    /// A signal interrupted the call before it completed.
    pub const INTERRUPTED: Self = Self(4);
    /// An input or output error, the answer for an error with no number.
    pub const INPUT_OUTPUT: Self = Self(5);
    /// No memory: a registration of buffers past the user's limit of locked
    /// memory.
    pub const NO_MEMORY: Self = Self(12);
    /// The resource is busy: a work that holds a worker's ring asks for it
    /// again.
    pub const BUSY: Self = Self(16);
    /// The argument is not valid, such as a depth of zero.
    pub const INVALID: Self = Self(22);
    /// The kernel has no such system call.
    pub const NO_SYSTEM_CALL: Self = Self(38);
    /// The kernel does not support what the call asks for, such as a ring
    /// without stable submissions.
    pub const NOT_SUPPORTED: Self = Self(95);
    /// The operation runs already, so a cancel cannot stop it.
    pub const ALREADY: Self = Self(114);
    /// A cancel, or the failure of an entry linked before it, stopped the
    /// operation.
    pub const CANCELLED: Self = Self(125);
    /// The kernel's answer breaks the ring's protocol, such as an offset of a
    /// queue outside its mapping, or a mapping at address zero.
    pub const PROTOCOL: Self = Self(71);
}

impl From<std::io::Error> for Errno
{
    /// The error number of an error of the standard library, or
    /// [`Errno::INPUT_OUTPUT`] when it carries none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: std::io::Error) -> Self
    {
        error.raw_os_error().map_or(Self::INPUT_OUTPUT, Self::from)
    }
}

impl From<Errno> for u16
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(errno: Errno) -> Self
    {
        errno.0
    }
}

impl From<i32> for Errno
{
    /// The error number of a negative result, as a completion carries it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(negative: i32) -> Self
    {
        Self(u16::try_from(negative.unsigned_abs()).unwrap_or(u16::MAX))
    }
}

/// Set up a ring of `entries` submission entries; the kernel fills
/// `params` with the ring's sizes, offsets and features.
///
/// # Specification
/// - ensures: on `Ok`, the ring's descriptor, and `params` as the kernel fills
///   it.
/// - fails: the kernel's error number, such as [`Errno::PERMISSION`] or
///   [`Errno::NO_SYSTEM_CALL`] where the ring is not allowed or not built.
/// - panics: none.
/// - executable: none — the descriptor is a kernel object, which no predicate
///   reads.
///
/// # Adequacy
/// - hypothesis: L3 — a ring set up here completes a linked write, sync and
///   read in order.
/// - witness: `tests::io::a_linked_write_sync_and_read_complete_in_order`
pub fn setup(
    entries: Word,
    params: &mut io_uring_params,
) -> Result<OwnedFd, Errno>
{
    // SAFETY: `params` names one `io_uring_params` that the borrow keeps
    // valid and writable for the call.
    let answer = unsafe {
        arch::call2(
            Number(syscall::IO_URING_SETUP),
            Argument::word(entries),
            Argument::place(params),
        )
    }
    .word()?;
    let raw = i32::try_from(answer.0).map_err(|_overflow| Errno::PROTOCOL)?;
    // SAFETY: the kernel answers a fresh descriptor that nothing else owns.
    Ok(unsafe { OwnedFd::from_raw_fd(raw) })
}

/// Register `count` items of the table at `table` with `ring`, as `opcode`
/// names them: buffers or files.
///
/// # Specification
/// - ensures: on `Ok`, the kernel's answer, and the ring holds the table.
/// - fails: the kernel's error number.
/// - panics: none.
/// - executable: none — the registration is the kernel's.
///
/// # Safety
/// - unsafe invariants: `table` names `count` items of the kind that `opcode`
///   reads, valid for the call, and `opcode` writes no memory of the process.
///
/// # Adequacy
/// - hypothesis: L3 — buffers registered here carry a fixed write and read.
/// - witness: `tests::io::a_registered_buffer_carries_a_fixed_write_and_read`
pub unsafe fn register<T>(
    ring: BorrowedFd<'_>,
    opcode: Word,
    table: *const T,
    count: Word,
) -> Result<Word, Errno>
{
    // SAFETY: the caller's invariants hold for the table, and the opcode
    // reads it alone.
    unsafe {
        arch::call4_readonly(
            Number(syscall::IO_URING_REGISTER),
            Argument::descriptor(ring),
            Argument::word(opcode),
            Argument::pointer(table),
            Argument::word(count),
        )
    }
    .word()
}

/// Submit `submit` entries of `ring` and wait for `wait` completions.
///
/// # Specification
/// - ensures: on `Ok`, the count of entries that the kernel consumed.
/// - fails: the kernel's error number.
/// - panics: none.
/// - executable: none — the entries and the completions are the kernel's to
///   read and write.
///
/// # Safety
/// - unsafe invariants: each submitted entry names buffers that stay valid
///   until its completion, and the ring's mappings stay mapped.
///
/// # Adequacy
/// - hypothesis: L3 — three linked entries complete in order after one enter.
/// - witness: `tests::io::a_linked_write_sync_and_read_complete_in_order`
pub unsafe fn enter(
    ring: BorrowedFd<'_>,
    submit: Word,
    wait: Word,
    flags: Word,
) -> Result<Word, Errno>
{
    // SAFETY: the caller's invariants hold for the entries and the mappings;
    // the call takes no extended argument.
    unsafe {
        arch::call6(
            Number(syscall::IO_URING_ENTER),
            Argument::descriptor(ring),
            Argument::word(submit),
            Argument::word(wait),
            Argument::word(flags),
            Argument::pointer(core::ptr::null::<c_void>()),
            Argument::none(),
        )
    }
    .word()
}

/// The bytes of locked memory that the process may pin, as its soft limit
/// gives them, or none when the limit is infinite. A registration of buffers
/// counts against this limit.
///
/// # Specification
/// - ensures: on `Ok`, the soft limit of `RLIMIT_MEMLOCK` in bytes, or none for
///   `RLIM64_INFINITY`.
/// - fails: the kernel's error number.
/// - panics: none.
/// - executable: none — the limit is the kernel's.
///
/// # Errors
/// The kernel's error number.
///
/// # Adequacy
/// - hypothesis: L3 — the buffers that a ring registers stay within this limit,
///   and the rest come back unregistered.
/// - witness: `tests::io::a_refused_registration_runs_its_buffers_unregistered`
#[inline]
pub fn locked() -> Result<Option<Word>, Errno>
{
    let mut limit = uapi::rlimit64 {
        rlim_cur: 0,
        rlim_max: 0,
    };
    // SAFETY: `limit` names one `rlimit64` that the borrow keeps valid and
    // writable for the call, and the call sets no limit.
    let _answer = unsafe {
        arch::call6(
            Number(syscall::PRLIMIT64),
            Argument::word(Word(0)),
            Argument::word(Word::from(uapi::RLIMIT_MEMLOCK)),
            Argument::pointer(core::ptr::null::<c_void>()),
            Argument::place(&mut limit),
            Argument::none(),
            Argument::none(),
        )
    }
    .word()?;
    // The header spells `RLIM64_INFINITY` as each bit set, so the constant
    // reads as -1 and compares with the limit's signed form.
    Ok(
        (limit.rlim_cur.cast_signed() != i64::from(uapi::RLIM64_INFINITY))
            .then(|| Word(usize::try_from(limit.rlim_cur).unwrap_or(usize::MAX))),
    )
}

/// The first byte of a mapping that [`map`] made.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Mapped(NonNull<u8>);

impl Mapped
{
    /// The place of a `T` at `offset` bytes past the first byte.
    ///
    /// # Specification
    /// - requires: `offset` and a `T` past it lie inside the mapping.
    /// - ensures: the pointer `offset` bytes past the first byte, as a `T`.
    /// - panics: none.
    /// - executable: none — the predicate would repeat the addition.
    ///
    /// # Safety
    /// - unsafe invariants: `offset` and a `T` past it lie inside the mapping.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the queues read at the kernel's offsets carry a
    ///   linked write, sync and read to their completions.
    /// - witness: `tests::io::a_linked_write_sync_and_read_complete_in_order`
    #[inline]
    pub unsafe fn at<T>(
        self,
        offset: Word,
    ) -> NonNull<T>
    {
        // SAFETY: the caller's invariant keeps the result inside the mapping.
        unsafe { self.0.add(offset.0) }.cast::<T>()
    }
}

/// Map `length` bytes of `ring` at `offset`, shared and populated.
///
/// # Specification
/// - ensures: on `Ok`, the first byte of a fresh mapping of `length` bytes.
/// - fails: the kernel's error number.
/// - panics: none.
/// - executable: none — the mapping is the kernel's.
///
/// # Adequacy
/// - hypothesis: L3 — the queues mapped here carry a linked write, sync and
///   read to their completions.
/// - witness: `tests::io::a_linked_write_sync_and_read_complete_in_order`
pub fn map(
    ring: BorrowedFd<'_>,
    length: Word,
    offset: Word,
) -> Result<Mapped, Errno>
{
    /// Read and write.
    const PROTECTION: Word = Word(0x3);
    /// Shared with the kernel, and populated at once.
    const FLAGS: Word = Word(0x1 | 0x8000);
    // SAFETY: a fresh mapping at an address the kernel chooses touches no
    // memory that Rust owns.
    unsafe {
        arch::call6(
            Number(syscall::MMAP),
            Argument::none(),
            Argument::word(length),
            Argument::word(PROTECTION),
            Argument::word(FLAGS),
            Argument::descriptor(ring),
            Argument::word(offset),
        )
    }
    .pointer()
    .map(|start| Mapped(start.cast::<u8>()))
}

/// Unmap the `length` bytes at `start`.
///
/// # Specification
/// - ensures: the mapping is gone, or the kernel's error number.
/// - panics: none.
/// - executable: none — the mapping is the kernel's.
///
/// # Safety
/// - unsafe invariants: `start` and `length` name one whole mapping that
///   [`map`] made, and nothing reads or writes it after the call.
///
/// # Adequacy
/// - hypothesis: L3 — a ring dropped after its run leaves no mapping that Miri
///   or the kernel reports.
/// - witness: `tests::io::dropping_an_io_completes_its_submitted_writes`
pub unsafe fn unmap(
    start: Mapped,
    length: Word,
) -> Result<(), Errno>
{
    // SAFETY: the caller's invariants hold for the mapping.
    unsafe {
        arch::call2(
            Number(syscall::MUNMAP),
            Argument::pointer(start.0.as_ptr()),
            Argument::word(length),
        )
    }
    .word()
    .map(|_unit| ())
}
