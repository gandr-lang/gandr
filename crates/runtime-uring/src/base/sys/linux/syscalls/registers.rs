//! Encapsulation for system call arguments and return values.
//!
//! The inline-asm code paths do some amount of reordering of arguments; to
//! ensure that we don't accidentally misroute an argument or return value, we
//! use distinct types for each argument index and return value.
//!
//! # Safety
//!
//! The `into_asm` and `from_asm` methods are unsafe to use; they should only
//! be used by the syscall code which executes actual syscall machine
//! instructions.

use core::marker::PhantomData;

use ::std::os::fd::RawFd;

use crate::arg::Answer;
use crate::arg::Code;
use crate::arg::Count;
use crate::arg::Fd;
use crate::arg::Flags;
use crate::arg::Holds;
use crate::arg::Len;
use crate::base::sys::linux::errno::Errno;

// use super::c;
// use super::fd::RawFd;

/// To preserve provenance, syscall arguments and return values are passed as
/// pointer types. They need a type to point to, so we define a custom private
/// type, to prevent it from being used for anything else.
#[repr(transparent)]
pub struct Opaque(::core::ffi::c_void);

/// A machine word that a register of a system call holds, with no
/// provenance: a number that the kernel reads.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Word(pub usize);

impl From<Count<::core::ffi::c_uint>> for Word
{
    /// The count `value`, widened to a word as the kernel reads an
    /// `unsigned int`.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn from(value: Count<::core::ffi::c_uint>) -> Self
    {
        Self(usize::try_from(value.0).unwrap_or(usize::MAX))
    }
}

impl From<Code<::core::ffi::c_uint>> for Word
{
    /// The code `value`, widened to a word as the kernel reads an
    /// `unsigned int`.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn from(value: Code<::core::ffi::c_uint>) -> Self
    {
        Self(usize::try_from(value.0).unwrap_or(usize::MAX))
    }
}

impl From<Flags<::core::ffi::c_uint>> for Word
{
    /// The flags `value`, widened to a word as the kernel reads an
    /// `unsigned int`.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn from(value: Flags<::core::ffi::c_uint>) -> Self
    {
        Self(usize::try_from(value.0).unwrap_or(usize::MAX))
    }
}

impl From<Fd> for Word
{
    /// The bits of the descriptor `value`, widened to a word as the kernel
    /// reads an `unsigned int`.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn from(value: Fd) -> Self
    {
        Self(usize::try_from(value.0.cast_unsigned()).unwrap_or(usize::MAX))
    }
}

impl From<Len<usize>> for Word
{
    /// The length `value` in bytes, as the kernel reads a `size_t`.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn from(value: Len<usize>) -> Self
    {
        Self(value.0)
    }
}

// Argument numbers.
/// The first argument of a system call.
#[repr(transparent)]
pub struct A0(());
/// The second argument of a system call.
#[repr(transparent)]
pub struct A1(());
/// The third argument of a system call.
#[repr(transparent)]
pub struct A2(());
/// The fourth argument of a system call.
#[repr(transparent)]
pub struct A3(());
/// The fifth argument of a system call.
#[repr(transparent)]
pub struct A4(());
/// The sixth argument of a system call.
#[repr(transparent)]
pub struct A5(());
/// The seventh argument of a system call, which MIPS alone has.
#[cfg(any(target_arch = "mips", target_arch = "mips32r6"))]
#[repr(transparent)]
pub struct A6(());
/// The socket argument of a system call on x86.
#[cfg(target_arch = "x86")]
pub struct SocketArg;

/// The index of an argument's register.
pub trait ArgNumber: private::ArgNumber
{
}
impl ArgNumber for A0
{
}
impl ArgNumber for A1
{
}
impl ArgNumber for A2
{
}
impl ArgNumber for A3
{
}
impl ArgNumber for A4
{
}
impl ArgNumber for A5
{
}

// Return value numbers.
/// The register that a system call answers in.
#[repr(transparent)]
pub struct R0(());

/// The index of the register that a system call answers in.
pub trait RetNumber: private::RetNumber
{
}
impl RetNumber for R0
{
}

/// One argument of a system call, in the register that `Num` names, which
/// may borrow memory or a descriptor for `'arg`.
#[must_use]
#[repr(transparent)]
pub struct ArgReg<'arg, Num>
where
    Num: ArgNumber,
{
    /// The register's value.
    raw: *mut Opaque,
    /// The borrow and the register's index.
    marker: PhantomData<(&'arg (), Num)>,
}

impl<Num> ArgReg<'_, Num>
where
    Num: ArgNumber,
{
    /// The argument whose register holds `raw`.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    pub const fn new(raw: *mut Opaque) -> Self
    {
        Self {
            raw,
            marker: PhantomData,
        }
    }

    /// The register's value, for the instruction alone.
    ///
    /// # Safety
    ///
    /// - unsafe invariants: the value goes to the system call instruction and
    ///   to no other use.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    pub const unsafe fn into_asm(self) -> *mut Opaque
    {
        self.raw
    }
}

/// The answer of a system call, in the register that `Num` names.
#[must_use]
#[repr(transparent)]
pub struct RetReg<Num>
where
    Num: RetNumber,
{
    /// The register's value.
    raw: *mut Opaque,
    /// The register's index.
    marker: PhantomData<Num>,
}

impl<Num> RetReg<Num>
where
    Num: RetNumber,
{
    /// The answer that the instruction leaves in its register.
    ///
    /// # Safety
    ///
    /// - unsafe invariants: `raw` is the value that the system call instruction
    ///   answers.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    pub const unsafe fn from_asm(raw: *mut Opaque) -> Self
    {
        Self {
            raw,
            marker: PhantomData,
        }
    }

    /// The answer as a number, which names no error.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    pub fn decode_usize(self) -> Answer<usize>
    {
        debug_assert!(
            !(-4095 .. 0).contains(&self.raw.addr().cast_signed()),
            "the answer names no error"
        );

        Answer(self.raw.addr())
    }

    /// The answer as a descriptor. A descriptor that the kernel answers fits
    /// 31 bits, and the largest descriptor stands for one that does not.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    pub fn decode_raw_fd(self) -> Fd
    {
        let Answer(bits) = self.decode_usize();
        let raw = RawFd::try_from(bits);
        debug_assert!(raw.is_ok(), "the descriptor fits 31 bits");
        Fd(raw.unwrap_or(RawFd::MAX))
    }

    /// The answer as a count. A count that the kernel answers fits 32 bits,
    /// and the largest count stands for one that does not.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    pub fn decode_c_uint(self) -> Answer<::core::ffi::c_uint>
    {
        let Answer(bits) = self.decode_usize();
        let uint = ::core::ffi::c_uint::try_from(bits);
        debug_assert!(uint.is_ok(), "the count fits 32 bits");
        Answer(uint.unwrap_or(::core::ffi::c_uint::MAX))
    }

    /// The error number that the answer names, in the encoded form of
    /// [`Errno`]: the error number negated in 16 bits, as the owner's
    /// `into_raw_os_error` reads it.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    pub fn decode_error_code(self) -> Code<u16>
    {
        debug_assert!(
            (-4095 .. 0).contains(&self.raw.addr().cast_signed()),
            "the answer names an error"
        );
        let errno = self.raw.addr().cast_signed().unsigned_abs();
        Code(u16::try_from(errno).unwrap_or(u16::MAX).wrapping_neg())
    }

    /// Whether the answer names an error.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    pub fn errno_contains(&self) -> Holds
    {
        Errno::contains(Answer(self.raw.addr().cast_signed()))
    }
}

/// The number of a system call on this architecture, which the call borrows
/// for `'arg`.
#[repr(transparent)]
pub struct SyscallNumber<'arg>
{
    /// The number.
    val: usize,
    /// The borrow.
    marker: PhantomData<&'arg ()>,
}

impl SyscallNumber<'_>
{
    /// The system call that `val` numbers.
    ///
    /// # Specification
    ///
    /// trivial.
    #[expect(
        clippy::as_conversions,
        reason = "a const fn cannot call `usize::from`, and a u32 widens into a usize whole on each 64-bit target of the base"
    )]
    #[inline]
    pub const fn new(val: Code<u32>) -> Self
    {
        let val = val.0 as usize;
        SyscallNumber {
            val,
            marker: PhantomData,
        }
    }

    /// The number, as the instruction takes it: a pointer with no
    /// provenance.
    ///
    /// # Safety
    ///
    /// - unsafe invariants: the value goes to the system call instruction and
    ///   to no other use.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    pub const unsafe fn into_asm(self) -> *mut Opaque
    {
        ::core::ptr::without_provenance_mut(self.val)
    }
}

/// The traits that no other module implements.
mod private
{
    /// The index of an argument's register.
    pub trait ArgNumber
    {
    }
    impl self::ArgNumber for super::A0
    {
    }
    impl self::ArgNumber for super::A1
    {
    }
    impl self::ArgNumber for super::A2
    {
    }
    impl self::ArgNumber for super::A3
    {
    }
    impl self::ArgNumber for super::A4
    {
    }
    impl self::ArgNumber for super::A5
    {
    }
    impl self::ArgNumber for super::R0
    {
    }

    /// The index of an answer's register.
    pub trait RetNumber
    {
    }
    impl self::RetNumber for super::R0
    {
    }
}
