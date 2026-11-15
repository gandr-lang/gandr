//! The system call instruction of s390x. The number goes in `r1`, and the
//! arguments go in `r2` to `r7`. The answer comes back in `r2`.

use core::arch::asm;

use crate::base::sys::linux::syscalls::registers::A0;
use crate::base::sys::linux::syscalls::registers::A1;
use crate::base::sys::linux::syscalls::registers::A2;
use crate::base::sys::linux::syscalls::registers::A3;
use crate::base::sys::linux::syscalls::registers::A4;
use crate::base::sys::linux::syscalls::registers::A5;
use crate::base::sys::linux::syscalls::registers::ArgReg;
use crate::base::sys::linux::syscalls::registers::R0;
use crate::base::sys::linux::syscalls::registers::RetReg;
use crate::base::sys::linux::syscalls::registers::SyscallNumber;

/// Issues the system call `nr` with two arguments.
///
/// # Safety
///
/// - unsafe invariants: each pointer argument names memory that is valid for
///   the call's access, and the caller allows each effect of the call.
///
/// # Specification
///
/// - ensures: the kernel's answer.
/// - panics: none.
/// - executable: none — the call's effect is the kernel's.
///
/// # Adequacy
///
/// - hypothesis: L3 — a ring that this call sets up answers its descriptor.
/// - witness: `base::io_uring::test::setup`
#[inline]
pub unsafe fn syscall2(
    nr: SyscallNumber<'_>,
    a0: ArgReg<'_, A0>,
    a1: ArgReg<'_, A1>,
) -> RetReg<R0>
{
    let r0;
    // SAFETY: the number goes to the instruction alone.
    let nr = unsafe { nr.into_asm() };
    // SAFETY: the argument goes to the instruction alone.
    let a0 = unsafe { a0.into_asm() };
    // SAFETY: the argument goes to the instruction alone.
    let a1 = unsafe { a1.into_asm() };
    // SAFETY: the caller's invariants hold for the arguments, and the block
    // declares each register that the instruction overwrites and touches no
    // stack.
    unsafe {
        asm!(
            "svc 0",
            in("r1") nr,
            inlateout("r2") a0 => r0,
            in("r3") a1,
            options(nostack, preserves_flags)
        );
    }
    // SAFETY: `r0` is the value that the instruction answers.
    unsafe { RetReg::from_asm(r0) }
}

/// Issues the system call `nr` with four arguments, which writes no memory of
/// the process.
///
/// # Safety
///
/// - unsafe invariants: each pointer argument names memory that is valid for
///   the call's reads, and the call writes no memory of the process.
///
/// # Specification
///
/// - ensures: the kernel's answer.
/// - panics: none.
/// - executable: none — the call's effect is the kernel's.
///
/// # Adequacy
///
/// - hypothesis: L3 — a table of files that this call registers on a ring
///   answers zero, and so does its unregistration.
/// - witness: `base::io_uring::test::register`
#[inline]
pub unsafe fn syscall4_readonly(
    nr: SyscallNumber<'_>,
    a0: ArgReg<'_, A0>,
    a1: ArgReg<'_, A1>,
    a2: ArgReg<'_, A2>,
    a3: ArgReg<'_, A3>,
) -> RetReg<R0>
{
    let r0;
    // SAFETY: the number goes to the instruction alone.
    let nr = unsafe { nr.into_asm() };
    // SAFETY: the argument goes to the instruction alone.
    let a0 = unsafe { a0.into_asm() };
    // SAFETY: the argument goes to the instruction alone.
    let a1 = unsafe { a1.into_asm() };
    // SAFETY: the argument goes to the instruction alone.
    let a2 = unsafe { a2.into_asm() };
    // SAFETY: the argument goes to the instruction alone.
    let a3 = unsafe { a3.into_asm() };
    // SAFETY: the caller's invariants hold for the arguments, and they let
    // the block promise that it writes no memory. The block declares each
    // register that the instruction overwrites and touches no stack.
    unsafe {
        asm!(
            "svc 0",
            in("r1") nr,
            inlateout("r2") a0 => r0,
            in("r3") a1,
            in("r4") a2,
            in("r5") a3,
            options(nostack, preserves_flags, readonly)
        );
    }
    // SAFETY: `r0` is the value that the instruction answers.
    unsafe { RetReg::from_asm(r0) }
}

// NOTE: s390x has some special cases that we would need to handle differently
// if we were to support all syscalls. For example, the `mmap` syscall uses the
// old struct-based interface, where the arguments are packed into a struct.
/// Issues the system call `nr` with six arguments.
///
/// # Safety
///
/// - unsafe invariants: each pointer argument names memory that is valid for
///   the call's access, and the caller allows each effect of the call.
///
/// # Specification
///
/// - ensures: the kernel's answer.
/// - panics: none.
/// - executable: none — the call's effect is the kernel's.
///
/// # Adequacy
///
/// - hypothesis: L3 — an enter that submits nothing and waits for nothing
///   answers zero.
/// - witness: `base::io_uring::test::enter`
#[inline]
pub unsafe fn syscall6(
    nr: SyscallNumber<'_>,
    a0: ArgReg<'_, A0>,
    a1: ArgReg<'_, A1>,
    a2: ArgReg<'_, A2>,
    a3: ArgReg<'_, A3>,
    a4: ArgReg<'_, A4>,
    a5: ArgReg<'_, A5>,
) -> RetReg<R0>
{
    let r0;
    // SAFETY: the number goes to the instruction alone.
    let nr = unsafe { nr.into_asm() };
    // SAFETY: the argument goes to the instruction alone.
    let a0 = unsafe { a0.into_asm() };
    // SAFETY: the argument goes to the instruction alone.
    let a1 = unsafe { a1.into_asm() };
    // SAFETY: the argument goes to the instruction alone.
    let a2 = unsafe { a2.into_asm() };
    // SAFETY: the argument goes to the instruction alone.
    let a3 = unsafe { a3.into_asm() };
    // SAFETY: the argument goes to the instruction alone.
    let a4 = unsafe { a4.into_asm() };
    // SAFETY: the argument goes to the instruction alone.
    let a5 = unsafe { a5.into_asm() };
    // SAFETY: the caller's invariants hold for the arguments, and the block
    // declares each register that the instruction overwrites and touches no
    // stack.
    unsafe {
        asm!(
            "svc 0",
            in("r1") nr,
            inlateout("r2") a0 => r0,
            in("r3") a1,
            in("r4") a2,
            in("r5") a3,
            in("r6") a4,
            in("r7") a5,
            options(nostack, preserves_flags)
        );
    }
    // SAFETY: `r0` is the value that the instruction answers.
    unsafe { RetReg::from_asm(r0) }
}
