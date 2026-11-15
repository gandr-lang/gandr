#![expect(clippy::undocumented_unsafe_blocks, reason = "WIP")]

use ::std::os::fd::AsRawFd as _;
use ::std::os::fd::BorrowedFd;
use ::std::os::fd::OwnedFd;

use crate::sys::linux::syscalls::convert::by_mut;
use crate::sys::linux::syscalls::convert::c_uint;
use crate::sys::linux::syscalls::convert::pass_usize;
use crate::sys::linux::syscalls::convert::raw_arg;
use crate::sys::linux::syscalls::convert::raw_fd;
use crate::sys::linux::syscalls::convert::ret_c_uint;
use crate::sys::linux::syscalls::convert::ret_owned_fd;
use crate::sys::linux::syscalls::registers::SyscallNumber;
use crate::sys::linux::syscalls::strategy::syscall2;
use crate::sys::linux::syscalls::strategy::syscall4_readonly;
use crate::sys::linux::syscalls::strategy::syscall6;
use crate::sys::linux::uapi::arch::__NR_io_uring_enter;
use crate::sys::linux::uapi::arch::__NR_io_uring_register;
use crate::sys::linux::uapi::arch::__NR_io_uring_setup;
use crate::sys::linux::uapi::arch::io_uring_params;

/// # Errors
#[inline]
pub fn io_uring_setup(entries: u32, params: &mut io_uring_params) -> crate::io::Result<OwnedFd> {
    let nr = SyscallNumber::new(__NR_io_uring_setup);
    let entries = c_uint(entries);
    let params = by_mut(params);
    let result = unsafe { syscall2(nr, entries, params) };
    unsafe { ret_owned_fd(result) }
}

/// # Errors
#[inline]
pub unsafe fn io_uring_register(
    fd: BorrowedFd<'_>,
    opcode: u32,
    arg: *const ::core::ffi::c_void,
    nr_args: u32,
) -> crate::io::Result<u32> {
    let nr = SyscallNumber::new(__NR_io_uring_register);
    let fd = {
        let fd = fd.as_raw_fd();
        unsafe { raw_fd(fd) }
    };
    let opcode = c_uint(opcode);
    let arg = {
        let arg = arg.cast_mut();
        let arg = arg.cast();
        raw_arg(arg)
    };
    let nr_args = c_uint(nr_args);
    let result = unsafe { syscall4_readonly(nr, fd, opcode, arg, nr_args) };
    ret_c_uint(result)
}

/// # Errors
#[inline]
pub unsafe fn io_uring_register_with(
    fd: BorrowedFd<'_>,
    opcode: u32,
    flags: u32,
    arg: *const ::core::ffi::c_void,
    nr_args: u32,
) -> crate::io::Result<u32> {
    let nr = SyscallNumber::new(__NR_io_uring_register);
    let fd = {
        let fd = fd.as_raw_fd();
        unsafe { raw_fd(fd) }
    };
    let opcode = {
        let opcode = opcode | flags;
        c_uint(opcode)
    };
    let arg = {
        let arg = arg.cast_mut();
        let arg = arg.cast();
        raw_arg(arg)
    };
    let nr_args = c_uint(nr_args);
    let result = unsafe { syscall4_readonly(nr, fd, opcode, arg, nr_args) };
    ret_c_uint(result)
}

/// # Errors
#[inline]
pub unsafe fn io_uring_enter(
    fd: BorrowedFd<'_>,
    to_submit: u32,
    min_complete: u32,
    flags: u32,
    arg: *const ::core::ffi::c_void,
    size: usize,
) -> crate::io::Result<u32> {
    let nr = SyscallNumber::new(__NR_io_uring_enter);
    let fd = {
        let fd = fd.as_raw_fd();
        unsafe { raw_fd(fd) }
    };
    let to_submit = c_uint(to_submit);
    let min_complete = c_uint(min_complete);
    let flags = c_uint(flags);
    let arg = {
        let arg = arg.cast_mut();
        let arg = arg.cast();
        raw_arg(arg)
    };
    let size = pass_usize(size);
    let result = unsafe { syscall6(nr, fd, to_submit, min_complete, flags, arg, size) };
    ret_c_uint(result)
}
