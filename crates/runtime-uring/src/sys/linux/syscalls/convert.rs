#![expect(
    clippy::as_conversions,
    clippy::cast_sign_loss,
    clippy::undocumented_unsafe_blocks,
    reason = "WIP"
)]

use ::core::marker::PhantomData;
use ::std::os::fd::FromRawFd as _;
use ::std::os::fd::OwnedFd;
use ::std::os::fd::RawFd;

use crate::sys::linux::errno::Errno;
use crate::sys::linux::syscalls::registers::ArgNumber;
use crate::sys::linux::syscalls::registers::ArgReg;
use crate::sys::linux::syscalls::registers::Opaque;
use crate::sys::linux::syscalls::registers::R0;
use crate::sys::linux::syscalls::registers::RetNumber;
use crate::sys::linux::syscalls::registers::RetReg;

#[inline]
pub(crate) const fn raw_arg<'arg, Num>(raw: *mut Opaque) -> ArgReg<'arg, Num>
where
    Num: ArgNumber,
{
    ArgReg {
        raw,
        marker: PhantomData,
    }
}

#[inline]
pub(crate) const unsafe fn raw_fd<'arg, Num>(fd: RawFd) -> ArgReg<'arg, Num>
where
    Num: ArgNumber,
{
    let fd = fd as ::core::ffi::c_uint;
    let fd = fd as usize;
    pass_usize(fd)
}

#[inline]
pub(crate) const fn pass_usize<'arg, Num>(val: usize) -> ArgReg<'arg, Num>
where
    Num: ArgNumber,
{
    let val = val as *mut Opaque;
    raw_arg(val)
}

#[inline]
pub(crate) const fn c_uint<'arg, Num>(val: ::core::ffi::c_uint) -> ArgReg<'arg, Num>
where
    Num: ArgNumber,
{
    let val = val as usize;
    pass_usize(val)
}

#[inline]
pub(crate) const fn by_mut<T, Num>(ptr: &mut T) -> ArgReg<'_, Num>
where
    T: Sized,
    Num: ArgNumber,
{
    let ptr = ::core::ptr::from_mut(ptr);
    unsafe { by_mut_ptr(ptr) }
}

#[inline]
pub(crate) const unsafe fn by_mut_ptr<'arg, T, Num>(ptr: *mut T) -> ArgReg<'arg, Num>
where
    T: Sized,
    Num: ArgNumber,
{
    let raw = ptr.cast();
    raw_arg(raw)
}

#[inline]
pub(crate) fn ret_c_uint(raw: RetReg<R0>) -> crate::io::Result<::core::ffi::c_uint> {
    try_decode_c_uint(raw)
}

#[inline]
pub(crate) unsafe fn ret_owned_fd(raw: RetReg<R0>) -> crate::io::Result<OwnedFd> {
    let raw_fd = unsafe { try_decode_raw_fd(raw) }?;
    let own_fd = unsafe { OwnedFd::from_raw_fd(raw_fd) };
    Ok(own_fd)
}

#[inline]
pub(crate) fn try_decode_c_uint<Num>(raw: RetReg<Num>) -> crate::io::Result<::core::ffi::c_uint>
where
    Num: RetNumber,
{
    if raw.errno_contains() {
        return Err(Errno(raw.decode_error_code()));
    }
    Ok(raw.decode_c_uint())
}

#[inline]
pub(crate) unsafe fn try_decode_raw_fd<Num>(raw: RetReg<Num>) -> crate::io::Result<RawFd>
where
    Num: RetNumber,
{
    if raw.errno_contains() {
        return Err(Errno(raw.decode_error_code()));
    }
    Ok(raw.decode_raw_fd())
}
