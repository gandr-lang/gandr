#![expect(
    clippy::as_conversions,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::missing_assert_message,
    clippy::unnecessary_cast,
    reason = "WIP"
)]

//! Encapsulation for system call arguments and return values.
//!
//! The inline-asm code paths do some amount of reordering of arguments; to
//! ensure that we don't accidentally misroute an argument or return value, we
//! use distinct types for each argument index and return value.
//!
//! # Safety
//!
//! The `ToAsm` and `FromAsm` traits are unsafe to use; they should only be
//! used by the syscall code which executes actual syscall machine
//! instructions.

use core::marker::PhantomData;

use ::std::os::fd::RawFd;

use crate::sys::linux::errno::Errno;

// use super::c;
// use super::fd::RawFd;

/// To preserve provenance, syscall arguments and return values are passed as
/// pointer types. They need a type to point to, so we define a custom private
/// type, to prevent it from being used for anything else.
#[repr(transparent)]
pub(crate) struct Opaque(::core::ffi::c_void);

// Argument numbers.
pub(crate) struct A0(());
pub(crate) struct A1(());
pub(crate) struct A2(());
pub(crate) struct A3(());
pub(crate) struct A4(());
pub(crate) struct A5(());
#[cfg(any(target_arch = "mips", target_arch = "mips32r6"))]
pub(crate) struct A6(());
#[cfg(target_arch = "x86")]
pub(crate) struct SocketArg;

pub(crate) trait ArgNumber: private::ArgNumber {}
impl ArgNumber for A0 {}
impl ArgNumber for A1 {}
impl ArgNumber for A2 {}
impl ArgNumber for A3 {}
impl ArgNumber for A4 {}
impl ArgNumber for A5 {}

// Return value numbers.
pub(crate) struct R0(());

pub(crate) trait RetNumber: private::RetNumber {}
impl RetNumber for R0 {}

#[must_use]
#[repr(transparent)]
pub(crate) struct ArgReg<'arg, Num>
where
    Num: ArgNumber,
{
    pub(crate) raw: *mut Opaque,
    pub(crate) marker: PhantomData<(&'arg (), Num)>,
}

impl<Num> ArgReg<'_, Num>
where
    Num: ArgNumber,
{
    #[inline]
    pub(crate) const unsafe fn into_asm(self) -> *mut Opaque {
        self.raw
    }
}

#[must_use]
#[repr(transparent)]
pub(crate) struct RetReg<Num>
where
    Num: RetNumber,
{
    raw: *mut Opaque,
    marker: PhantomData<Num>,
}

impl<Num> RetReg<Num>
where
    Num: RetNumber,
{
    #[inline]
    pub(crate) const unsafe fn from_asm(raw: *mut Opaque) -> Self {
        Self {
            raw,
            marker: PhantomData,
        }
    }

    #[inline]
    pub(crate) fn decode_usize(self) -> usize {
        debug_assert!(!(-4095..0).contains(&(self.raw as isize)));

        self.raw as usize
    }

    #[inline]
    pub(crate) fn decode_raw_fd(self) -> RawFd {
        let bits = self.decode_usize();
        let raw = bits as RawFd;
        debug_assert_eq!(raw as usize, bits);
        raw
    }

    #[inline]
    pub(crate) fn decode_c_uint(self) -> ::core::ffi::c_uint {
        let bits = self.decode_usize();
        let uint = bits as ::core::ffi::c_uint;
        debug_assert_eq!(uint as usize, bits);
        uint
    }

    #[inline]
    pub(crate) fn decode_error_code(self) -> u16 {
        debug_assert!((-4095..0).contains(&(self.raw as isize)));
        self.raw as u16
    }

    pub(crate) fn errno_contains(&self) -> bool {
        Errno::contains(self.raw as isize)
    }
}

#[repr(transparent)]
pub(crate) struct SyscallNumber<'arg> {
    pub(crate) val: usize,
    marker: PhantomData<&'arg ()>,
}

impl SyscallNumber<'_> {
    pub(crate) const fn new(val: u32) -> Self {
        let val = val as usize;
        SyscallNumber {
            val,
            marker: PhantomData,
        }
    }

    #[inline]
    pub(crate) const unsafe fn into_asm(self) -> *mut Opaque {
        self.val as usize as *mut Opaque
    }
}

mod private {
    pub trait ArgNumber {}
    impl self::ArgNumber for super::A0 {}
    impl self::ArgNumber for super::A1 {}
    impl self::ArgNumber for super::A2 {}
    impl self::ArgNumber for super::A3 {}
    impl self::ArgNumber for super::A4 {}
    impl self::ArgNumber for super::A5 {}
    impl self::ArgNumber for super::R0 {}

    pub trait RetNumber {}
    impl self::RetNumber for super::R0 {}
}
