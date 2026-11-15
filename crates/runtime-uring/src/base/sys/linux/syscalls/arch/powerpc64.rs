#![expect(clippy::undocumented_unsafe_blocks, reason = "WIP")]

//! On powerpc64le, Linux indicates success or failure using `cr0.SO` rather
//! than by returning a negative error code as most other architectures do. In
//! theory we could immediately translate this into a `Result`, and it'd save a
//! few branches. And in theory we could have specialized sequences for use
//! with syscalls that are known to never fail. However, those would require
//! more extensive changes in rustix's platform-independent code. For now, we
//! check the flag and negate the error value to make PowerPC 64 look like other
//! architectures.

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
            "sc",
            "bns 0f",
            "neg 3, 3",
            "0:",
            inlateout("r0") nr => _,
            inlateout("r3") a0 => r0,
            inlateout("r4") a1 => _,
            lateout("r5") _,
            lateout("r6") _,
            lateout("r7") _,
            lateout("r8") _,
            lateout("r9") _,
            lateout("r10") _,
            lateout("r11") _,
            lateout("r12") _,
            lateout("cr0") _,
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
            "sc",
            "bns 0f",
            "neg 3, 3",
            "0:",
            inlateout("r0") nr => _,
            inlateout("r3") a0 => r0,
            inlateout("r4") a1 => _,
            inlateout("r5") a2 => _,
            inlateout("r6") a3 => _,
            lateout("r7") _,
            lateout("r8") _,
            lateout("r9") _,
            lateout("r10") _,
            lateout("r11") _,
            lateout("r12") _,
            lateout("cr0") _,
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
            "sc",
            "bns 0f",
            "neg 3, 3",
            "0:",
            inlateout("r0") nr => _,
            inlateout("r3") a0 => r0,
            inlateout("r4") a1 => _,
            inlateout("r5") a2 => _,
            inlateout("r6") a3 => _,
            inlateout("r7") a4 => _,
            inlateout("r8") a5 => _,
            lateout("r9") _,
            lateout("r10") _,
            lateout("r11") _,
            lateout("r12") _,
            lateout("cr0") _,
            options(nostack, preserves_flags)
        );
    }
    unsafe { RetReg::from_asm(r0) }
}
