//! The system calls that the ring issues: each by the architecture's own
//! instruction, with no C library. The numbers come from the generated
//! table in `uapi`.

use core::arch::asm;
use core::ptr::NonNull;
use std::os::fd::AsRawFd as _;
use std::os::fd::BorrowedFd;
use std::os::fd::FromRawFd as _;
use std::os::fd::OwnedFd;

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

/// The number of a system call on this architecture.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Number(u32);

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
    /// The kernel has no such system call.
    pub const NO_SYSTEM_CALL: Self = Self(38);
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

/// The kernel's answers past this word are error numbers, from 1 to 4095.
const FIRST_ERROR: usize = usize::MAX.wrapping_sub(4_094);

/// Issue system call `number` with six argument words. The kernel reads
/// the words that the call takes and ignores the rest.
///
/// # Specification
/// - ensures: the call's answer, or the error number that it answers.
/// - panics: none.
/// - executable: none — the call's effect is the kernel's, and no predicate
///   reads it.
///
/// # Safety
/// - unsafe invariants: each word that the call reads as a pointer names memory
///   that is valid for the call's access, for the call's whole length, and the
///   caller allows each effect of the call on memory and on descriptors.
///
/// # Adequacy
/// - hypothesis: L3 — a ring set up, mapped and entered through this call
///   completes a linked write, sync and read in order.
/// - witness: `tests::ring::a_linked_write_sync_and_read_complete_in_order`
unsafe fn call(
    number: Number,
    words: [Word; 6],
) -> Result<Word, Errno>
{
    let [first, second, third, fourth, fifth, sixth] = words;
    let number = usize::try_from(number.0).unwrap_or(usize::MAX);
    let answer: usize;
    #[cfg(target_arch = "x86_64")]
    // SAFETY: the caller's invariants hold for the words; `syscall` clobbers
    // `rcx` and `r11`, which the block declares, and touches no stack.
    unsafe {
        asm!(
            "syscall",
            inlateout("rax") number => answer,
            in("rdi") first.0,
            in("rsi") second.0,
            in("rdx") third.0,
            in("r10") fourth.0,
            in("r8") fifth.0,
            in("r9") sixth.0,
            lateout("rcx") _,
            lateout("r11") _,
            options(nostack, preserves_flags),
        );
    }
    #[cfg(target_arch = "riscv64")]
    // SAFETY: the caller's invariants hold for the words; `ecall` answers in
    // `a0` and touches no stack.
    unsafe {
        asm!(
            "ecall",
            in("a7") number,
            inlateout("a0") first.0 => answer,
            in("a1") second.0,
            in("a2") third.0,
            in("a3") fourth.0,
            in("a4") fifth.0,
            in("a5") sixth.0,
            options(nostack, preserves_flags),
        );
    }
    if answer >= FIRST_ERROR {
        Err(Errno(
            u16::try_from(answer.wrapping_neg()).unwrap_or(u16::MAX),
        ))
    }
    else {
        Ok(Word(answer))
    }
}

/// A word of zero, for each argument that a call does not take.
const NONE: Word = Word(0);

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
/// - witness: `tests::ring::a_linked_write_sync_and_read_complete_in_order`
pub fn setup(
    entries: Word,
    params: &mut io_uring_params,
) -> Result<OwnedFd, Errno>
{
    let params = Word(core::ptr::from_mut(params).addr());
    // SAFETY: `params` names one `io_uring_params` that the borrow keeps
    // valid and writable for the call.
    let answer = unsafe {
        call(Number(syscall::IO_URING_SETUP), [
            entries, params, NONE, NONE, NONE, NONE,
        ])
    }?;
    let raw = i32::try_from(answer.0).map_err(|_overflow| Errno::NO_SYSTEM_CALL)?;
    // SAFETY: the kernel answers a fresh descriptor that nothing else owns.
    Ok(unsafe { OwnedFd::from_raw_fd(raw) })
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
/// - witness: `tests::ring::a_linked_write_sync_and_read_complete_in_order`
pub unsafe fn enter(
    ring: BorrowedFd<'_>,
    submit: Word,
    wait: Word,
    flags: Word,
) -> Result<Word, Errno>
{
    let ring = Word(usize::try_from(ring.as_raw_fd()).unwrap_or(usize::MAX));
    // SAFETY: the caller's invariants hold for the entries and the mappings.
    unsafe {
        call(Number(syscall::IO_URING_ENTER), [
            ring, submit, wait, flags, NONE, NONE,
        ])
    }
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
    /// - witness: `tests::ring::a_linked_write_sync_and_read_complete_in_order`
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
/// - witness: `tests::ring::a_linked_write_sync_and_read_complete_in_order`
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
    let ring = Word(usize::try_from(ring.as_raw_fd()).unwrap_or(usize::MAX));
    // SAFETY: a fresh mapping at an address the kernel chooses touches no
    // memory that Rust owns.
    let answer = unsafe {
        call(Number(syscall::MMAP), [
            NONE, length, PROTECTION, FLAGS, ring, offset,
        ])
    }?;
    NonNull::new(core::ptr::with_exposed_provenance_mut::<u8>(answer.0))
        .map(Mapped)
        .ok_or(Errno::NO_SYSTEM_CALL)
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
/// - witness: `tests::ring::a_linked_write_sync_and_read_complete_in_order`
pub unsafe fn unmap(
    start: Mapped,
    length: Word,
) -> Result<(), Errno>
{
    // SAFETY: the caller's invariants hold for the mapping.
    unsafe {
        call(Number(syscall::MUNMAP), [
            Word(start.0.addr().get()),
            length,
            NONE,
            NONE,
            NONE,
            NONE,
        ])
    }
    .map(|_unit| ())
}
