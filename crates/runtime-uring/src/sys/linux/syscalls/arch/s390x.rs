#![expect(clippy::undocumented_unsafe_blocks, reason = "WIP")]

use core::arch::asm;

use crate::sys::linux::syscalls::registers::A0;
use crate::sys::linux::syscalls::registers::A1;
use crate::sys::linux::syscalls::registers::A2;
use crate::sys::linux::syscalls::registers::A3;
use crate::sys::linux::syscalls::registers::A4;
use crate::sys::linux::syscalls::registers::A5;
use crate::sys::linux::syscalls::registers::ArgReg;
use crate::sys::linux::syscalls::registers::R0;
use crate::sys::linux::syscalls::registers::RetReg;
use crate::sys::linux::syscalls::registers::SyscallNumber;

#[inline]
pub(crate) unsafe fn syscall2(nr: SyscallNumber<'_>, a0: ArgReg<'_, A0>, a1: ArgReg<'_, A1>) -> RetReg<R0> {
    let r0;
    let nr = unsafe { nr.into_asm() };
    let a0 = unsafe { a0.into_asm() };
    let a1 = unsafe { a1.into_asm() };
    unsafe {
        asm!(
            "svc 0",
            in("r1") nr,
            inlateout("r2") a0 => r0,
            in("r3") a1,
            options(nostack, preserves_flags)
        );
    }
    unsafe { RetReg::from_asm(r0) }
}

#[inline]
pub(crate) unsafe fn syscall4_readonly(
    nr: SyscallNumber<'_>,
    a0: ArgReg<'_, A0>,
    a1: ArgReg<'_, A1>,
    a2: ArgReg<'_, A2>,
    a3: ArgReg<'_, A3>,
) -> RetReg<R0> {
    let r0;
    let nr = unsafe { nr.into_asm() };
    let a0 = unsafe { a0.into_asm() };
    let a1 = unsafe { a1.into_asm() };
    let a2 = unsafe { a2.into_asm() };
    let a3 = unsafe { a3.into_asm() };
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
    unsafe { RetReg::from_asm(r0) }
}

// NOTE: s390x has some special cases that we would need to handle differently
// if we were to support all syscalls. For example, the `mmap` syscall uses the
// old struct-based interface, where the arguments are packed into a struct.
#[inline]
pub(crate) unsafe fn syscall6(
    nr: SyscallNumber<'_>,
    a0: ArgReg<'_, A0>,
    a1: ArgReg<'_, A1>,
    a2: ArgReg<'_, A2>,
    a3: ArgReg<'_, A3>,
    a4: ArgReg<'_, A4>,
    a5: ArgReg<'_, A5>,
) -> RetReg<R0> {
    let r0;
    let nr = unsafe { nr.into_asm() };
    let a0 = unsafe { a0.into_asm() };
    let a1 = unsafe { a1.into_asm() };
    let a2 = unsafe { a2.into_asm() };
    let a3 = unsafe { a3.into_asm() };
    let a4 = unsafe { a4.into_asm() };
    let a5 = unsafe { a5.into_asm() };
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
    unsafe { RetReg::from_asm(r0) }
}
