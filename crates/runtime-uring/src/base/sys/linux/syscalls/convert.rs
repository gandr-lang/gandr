//! The conversions of a system call's arguments into their registers, and of
//! its answer out of its register.

use ::std::os::fd::FromRawFd as _;
use ::std::os::fd::OwnedFd;

use crate::arg::Answer;
use crate::arg::Fd;
use crate::base::sys::linux::errno::Errno;
use crate::base::sys::linux::syscalls::registers::ArgNumber;
use crate::base::sys::linux::syscalls::registers::ArgReg;
use crate::base::sys::linux::syscalls::registers::Opaque;
use crate::base::sys::linux::syscalls::registers::R0;
use crate::base::sys::linux::syscalls::registers::RetNumber;
use crate::base::sys::linux::syscalls::registers::RetReg;
use crate::base::sys::linux::syscalls::registers::Word;

/// The argument whose register holds `raw`.
///
/// # Specification
///
/// trivial.
#[inline]
pub const fn raw_arg<'arg, Num>(raw: *mut Opaque) -> ArgReg<'arg, Num>
where
    Num: ArgNumber,
{
    ArgReg::new(raw)
}

/// The descriptor `fd` as an argument: its bits, as the kernel reads an
/// `unsigned int`.
///
/// # Safety
///
/// - unsafe invariants: `fd` stays open, or names the ring's registered index,
///   for the call that takes the argument.
///
/// # Specification
///
/// trivial.
#[inline]
pub unsafe fn raw_fd<'arg, Num>(fd: Fd) -> ArgReg<'arg, Num>
where
    Num: ArgNumber,
{
    pass_usize(Word::from(fd))
}

/// The word `val` as an argument: a pointer with no provenance.
///
/// # Specification
///
/// trivial.
#[inline]
pub const fn pass_usize<'arg, Num>(val: Word) -> ArgReg<'arg, Num>
where
    Num: ArgNumber,
{
    let val = ::core::ptr::without_provenance_mut(val.0);
    raw_arg(val)
}

/// The 32-bit value `val` as an argument: a count, a code or a set of flags,
/// widened to a word.
///
/// # Specification
///
/// trivial.
#[inline]
pub fn c_uint<'arg, Num, Val>(val: Val) -> ArgReg<'arg, Num>
where
    Num: ArgNumber,
    Val: Into<Word>,
{
    pass_usize(val.into())
}

/// The place of `ptr` as an argument, which the kernel may write for the
/// borrow.
///
/// # Specification
///
/// trivial.
#[inline]
pub const fn by_mut<T, Num>(ptr: &mut T) -> ArgReg<'_, Num>
where
    T: Sized,
    Num: ArgNumber,
{
    let ptr = ::core::ptr::from_mut(ptr);
    // SAFETY: the pointer comes from a borrow, which stays valid and
    // writable for the argument's lifetime.
    unsafe { by_mut_ptr(ptr) }
}

/// The pointer `ptr` as an argument, with its provenance.
///
/// # Safety
///
/// - unsafe invariants: `ptr` names memory that stays valid for the access of
///   the call that takes the argument.
///
/// # Specification
///
/// trivial.
#[inline]
pub const unsafe fn by_mut_ptr<'arg, T, Num>(ptr: *mut T) -> ArgReg<'arg, Num>
where
    T: Sized,
    Num: ArgNumber,
{
    let raw = ptr.cast();
    raw_arg(raw)
}

/// The answer `raw` as a count, or the error number it names.
///
/// # Errors
///
/// The answer names an error number.
///
/// # Specification
///
/// - ensures: on `Ok`, the count that the kernel answers.
/// - fails: the error number that the answer names.
/// - panics: none.
/// - executable: none — the answer is the kernel's, observable only by a call.
///
/// # Adequacy
///
/// - hypothesis: L3 — an answer at or above zero is the count, and an answer in
///   `-4095..0` is its error number.
/// - witness: `base::io_uring::test::register`
/// - witness: `base::io_uring::test::enter`
#[inline]
pub fn ret_c_uint(raw: RetReg<R0>) -> crate::base::io::Result<Answer<::core::ffi::c_uint>>
{
    try_decode_c_uint(raw)
}

/// The answer `raw` as a descriptor that the caller owns, or the error
/// number it names.
///
/// # Errors
///
/// The answer names an error number.
///
/// # Safety
///
/// - unsafe invariants: `raw` is the answer of a call that gives a new
///   descriptor, which nothing else owns.
///
/// # Specification
///
/// - ensures: on `Ok`, the descriptor that the kernel answers, owned.
/// - fails: the error number that the answer names.
/// - panics: none.
/// - executable: none — the answer is the kernel's, observable only by a call.
///
/// # Adequacy
///
/// - hypothesis: L3 — an answer at or above zero is the new descriptor, and an
///   answer in `-4095..0` is its error number.
/// - witness: `base::io_uring::test::setup`
/// - witness: `base::io_uring::test::setup_refuses_no_entries`
#[inline]
pub unsafe fn ret_owned_fd(raw: RetReg<R0>) -> crate::base::io::Result<OwnedFd>
{
    // SAFETY: the caller gives the answer of a call that gives a descriptor.
    let Fd(raw_fd) = unsafe { try_decode_raw_fd(raw) }?;
    // SAFETY: the kernel answers a new descriptor, which nothing else owns.
    let own_fd = unsafe { OwnedFd::from_raw_fd(raw_fd) };
    Ok(own_fd)
}

/// The answer `raw` as a count, or the error number it names.
///
/// # Errors
///
/// The answer names an error number.
///
/// # Specification
///
/// - ensures: on `Ok`, the count that the kernel answers.
/// - fails: the error number that the answer names.
/// - panics: none.
/// - executable: none — the answer is the kernel's, observable only by a call.
///
/// # Adequacy
///
/// - hypothesis: L3 — as [`ret_c_uint`].
/// - witness: `base::io_uring::test::register`
/// - witness: `base::io_uring::test::enter`
#[inline]
pub fn try_decode_c_uint<Num>(
    raw: RetReg<Num>
) -> crate::base::io::Result<Answer<::core::ffi::c_uint>>
where
    Num: RetNumber,
{
    if raw.errno_contains().0 {
        return Err(Errno::from_encoded(raw.decode_error_code()));
    }
    Ok(raw.decode_c_uint())
}

/// The answer `raw` as a descriptor, or the error number it names.
///
/// # Errors
///
/// The answer names an error number.
///
/// # Safety
///
/// - unsafe invariants: `raw` is the answer of a call that gives a descriptor.
///
/// # Specification
///
/// - ensures: on `Ok`, the descriptor that the kernel answers.
/// - fails: the error number that the answer names.
/// - panics: none.
/// - executable: none — the answer is the kernel's, observable only by a call.
///
/// # Adequacy
///
/// - hypothesis: L3 — as [`ret_owned_fd`].
/// - witness: `base::io_uring::test::setup`
/// - witness: `base::io_uring::test::setup_refuses_no_entries`
#[inline]
pub unsafe fn try_decode_raw_fd<Num>(raw: RetReg<Num>) -> crate::base::io::Result<Fd>
where
    Num: RetNumber,
{
    if raw.errno_contains().0 {
        return Err(Errno::from_encoded(raw.decode_error_code()));
    }
    Ok(raw.decode_raw_fd())
}
