//! The ring's three system calls: `io_uring_setup`, `io_uring_register` and
//! `io_uring_enter`.

use ::std::os::fd::AsRawFd as _;
use ::std::os::fd::BorrowedFd;
use ::std::os::fd::OwnedFd;

use crate::arg::Answer;
use crate::arg::Code;
use crate::arg::Count;
use crate::arg::Fd;
use crate::arg::Flags;
use crate::arg::Len;
use crate::base::sys::linux::syscalls::convert::by_mut;
use crate::base::sys::linux::syscalls::convert::c_uint;
use crate::base::sys::linux::syscalls::convert::pass_usize;
use crate::base::sys::linux::syscalls::convert::raw_arg;
use crate::base::sys::linux::syscalls::convert::raw_fd;
use crate::base::sys::linux::syscalls::convert::ret_c_uint;
use crate::base::sys::linux::syscalls::convert::ret_owned_fd;
use crate::base::sys::linux::syscalls::registers::SyscallNumber;
use crate::base::sys::linux::syscalls::strategy::syscall2;
use crate::base::sys::linux::syscalls::strategy::syscall4_readonly;
use crate::base::sys::linux::syscalls::strategy::syscall6;
use crate::base::sys::linux::uapi::arch::__NR_io_uring_enter;
use crate::base::sys::linux::uapi::arch::__NR_io_uring_register;
use crate::base::sys::linux::uapi::arch::__NR_io_uring_setup;
use crate::base::sys::linux::uapi::arch::io_uring_params;

/// Sets up a ring of `entries` submission entries. The kernel fills `params`
/// with the ring's sizes, offsets and features.
///
/// # Errors
///
/// The kernel refuses the setup and answers its error number.
///
/// # Specification
///
/// - ensures: on `Ok`, the ring's descriptor, owned, and `params` as the kernel
///   fills it.
/// - fails: the kernel's error number, such as `EPERM` where a policy refuses
///   the ring.
/// - panics: none.
/// - executable: none — the descriptor is a kernel object, which no predicate
///   reads.
///
/// # Adequacy
///
/// - hypothesis: L3 — a setup of two entries answers a descriptor.
/// - witness: `base::io_uring::test::setup`
#[inline]
pub fn io_uring_setup(
    entries: Count<u32>,
    params: &mut io_uring_params,
) -> crate::base::io::Result<OwnedFd>
{
    let nr = SyscallNumber::new(Code(__NR_io_uring_setup));
    let entries = c_uint(entries);
    let params = by_mut(params);
    // SAFETY: `params` names one `io_uring_params` that the borrow keeps
    // valid and writable for the call.
    let result = unsafe { syscall2(nr, entries, params) };
    // SAFETY: a setup answers a new descriptor, which nothing else owns.
    unsafe { ret_owned_fd(result) }
}

/// Registers the `nr_args` items at `arg` with the ring `fd`, as `opcode`
/// names them.
///
/// # Errors
///
/// The kernel refuses the registration and answers its error number.
///
/// # Safety
///
/// - unsafe invariants: `arg` names `nr_args` items of the kind that `opcode`
///   reads, valid for the call, and `opcode` writes no memory of the process.
///
/// # Specification
///
/// - ensures: on `Ok`, the kernel's answer.
/// - fails: the kernel's error number.
/// - panics: none.
/// - executable: none — the registration is the kernel's.
///
/// # Adequacy
///
/// - hypothesis: L3 — a table of one file registers on a ring and unregisters.
/// - witness: `base::io_uring::test::register`
#[inline]
pub unsafe fn io_uring_register(
    fd: BorrowedFd<'_>,
    opcode: Code<u32>,
    arg: *const ::core::ffi::c_void,
    nr_args: Count<u32>,
) -> crate::base::io::Result<Answer<u32>>
{
    let nr = SyscallNumber::new(Code(__NR_io_uring_register));
    let fd = {
        let fd = Fd(fd.as_raw_fd());
        // SAFETY: the borrow keeps the ring's descriptor open for the call.
        unsafe { raw_fd(fd) }
    };
    let opcode = c_uint(opcode);
    let arg = {
        let arg = arg.cast_mut();
        let arg = arg.cast();
        raw_arg(arg)
    };
    let nr_args = c_uint(nr_args);
    // SAFETY: the caller's invariants hold for the table, and the opcode
    // reads it alone.
    let result = unsafe { syscall4_readonly(nr, fd, opcode, arg, nr_args) };
    ret_c_uint(result)
}

/// Registers the `nr_args` items at `arg` with the ring `fd`, as `opcode`
/// names them, with the flags `flags` joined to the opcode.
///
/// # Errors
///
/// The kernel refuses the registration and answers its error number.
///
/// # Safety
///
/// - unsafe invariants: `fd` is the ring's descriptor, or its registered index
///   when `flags` names one. `arg` names `nr_args` items of the kind that
///   `opcode` reads, valid for the call, and `opcode` writes no memory of the
///   process.
///
/// # Specification
///
/// - ensures: on `Ok`, the kernel's answer.
/// - fails: the kernel's error number.
/// - panics: none.
/// - executable: none — the registration is the kernel's.
///
/// # Adequacy
///
/// - hypothesis: L3 — the unregistration of a table of one file answers zero.
/// - witness: `base::io_uring::test::register`
#[inline]
pub unsafe fn io_uring_register_with(
    fd: BorrowedFd<'_>,
    opcode: Code<u32>,
    flags: Flags<u32>,
    arg: *const ::core::ffi::c_void,
    nr_args: Count<u32>,
) -> crate::base::io::Result<Answer<u32>>
{
    let nr = SyscallNumber::new(Code(__NR_io_uring_register));
    let fd = {
        let fd = Fd(fd.as_raw_fd());
        // SAFETY: the borrow keeps the ring's descriptor open for the call,
        // or the caller gives the ring's registered index.
        unsafe { raw_fd(fd) }
    };
    let opcode = {
        let opcode = Code(opcode.0 | flags.0);
        c_uint(opcode)
    };
    let arg = {
        let arg = arg.cast_mut();
        let arg = arg.cast();
        raw_arg(arg)
    };
    let nr_args = c_uint(nr_args);
    // SAFETY: the caller's invariants hold for the table, and the opcode
    // reads it alone.
    let result = unsafe { syscall4_readonly(nr, fd, opcode, arg, nr_args) };
    ret_c_uint(result)
}

/// Submits `to_submit` entries of the ring `fd` and waits for `min_complete`
/// completions, as `flags` asks. `arg` and `size` give the extended argument.
///
/// # Errors
///
/// The kernel refuses the call and answers its error number.
///
/// # Safety
///
/// - unsafe invariants: each submitted entry names memory that stays valid
///   until its completion, the ring's mappings stay mapped, and `arg` names
///   `size` bytes of the extended argument that `flags` names, or is null.
///
/// # Specification
///
/// - ensures: on `Ok`, the count of entries that the kernel consumed.
/// - fails: the kernel's error number.
/// - panics: none.
/// - executable: none — the entries and the completions are the kernel's to
///   read and write.
///
/// # Adequacy
///
/// - hypothesis: L3 — an enter that submits nothing and waits for nothing
///   answers zero.
/// - witness: `base::io_uring::test::enter`
#[inline]
pub unsafe fn io_uring_enter(
    fd: BorrowedFd<'_>,
    to_submit: Count<u32>,
    min_complete: Count<u32>,
    flags: Flags<u32>,
    arg: *const ::core::ffi::c_void,
    size: Len<usize>,
) -> crate::base::io::Result<Answer<u32>>
{
    let nr = SyscallNumber::new(Code(__NR_io_uring_enter));
    let fd = {
        let fd = Fd(fd.as_raw_fd());
        // SAFETY: the borrow keeps the ring's descriptor open for the call.
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
    let size = pass_usize(size.into());
    // SAFETY: the caller's invariants hold for the entries, the mappings and
    // the extended argument.
    let result = unsafe { syscall6(nr, fd, to_submit, min_complete, flags, arg, size) };
    ret_c_uint(result)
}
