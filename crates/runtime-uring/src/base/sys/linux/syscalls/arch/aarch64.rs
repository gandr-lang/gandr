#![expect(clippy::undocumented_unsafe_blocks, reason = "WIP")]

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

#[inline]
pub(crate) unsafe fn syscall2(
    nr: SyscallNumber<'_>,
    a0: ArgReg<'_, A0>,
    a1: ArgReg<'_, A1>,
) -> RetReg<R0>
{
    let r0;
    let nr = unsafe { nr.into_asm() };
    let a0 = unsafe { a0.into_asm() };
    let a1 = unsafe { a1.into_asm() };
    unsafe {
        asm!(
            "svc 0",
            in("x8") nr,
            inlateout("x0") a0 => r0,
            in("x1") a1,
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
) -> RetReg<R0>
{
    let r0;
    let nr = unsafe { nr.into_asm() };
    let a0 = unsafe { a0.into_asm() };
    let a1 = unsafe { a1.into_asm() };
    let a2 = unsafe { a2.into_asm() };
    let a3 = unsafe { a3.into_asm() };
    unsafe {
        asm!(
            "svc 0",
            in("x8") nr,
            inlateout("x0") a0 => r0,
            in("x1") a1,
            in("x2") a2,
            in("x3") a3,
            options(nostack, preserves_flags, readonly)
        );
    }
    unsafe { RetReg::from_asm(r0) }
}

#[inline]
pub(crate) unsafe fn syscall6(
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
            in("x8") nr,
            inlateout("x0") a0 => r0,
            in("x1") a1,
            in("x2") a2,
            in("x3") a3,
            in("x4") a4,
            in("x5") a5,
            options(nostack, preserves_flags)
        );
    }
    unsafe { RetReg::from_asm(r0) }
}
