//! The system call instruction of riscv64: the number in `a7`, the
//! arguments in `a0` to `a5`, the answer in `a0`.

use core::arch::asm;

use crate::sys::registers::Answer;
use crate::sys::registers::Argument;
use crate::sys::registers::Fifth;
use crate::sys::registers::First;
use crate::sys::registers::Fourth;
use crate::sys::registers::Number;
use crate::sys::registers::Second;
use crate::sys::registers::Sixth;
use crate::sys::registers::Third;

/// Issue system call `number` with two arguments.
///
/// # Specification
/// - ensures: the kernel's answer.
/// - panics: none.
/// - executable: none — the call's effect is the kernel's.
///
/// # Safety
/// - unsafe invariants: each pointer argument names memory that is valid for
///   the call's access, and the caller allows each effect of the call.
///
/// # Adequacy
/// - hypothesis: L3 — a ring set up and unmapped through this call completes a
///   linked write, sync and read in order.
/// - witness: `tests::io::a_linked_write_sync_and_read_complete_in_order`
#[inline]
pub unsafe fn call2(
    number: Number,
    first: Argument<'_, First>,
    second: Argument<'_, Second>,
) -> Answer
{
    let answer;
    // SAFETY: the caller's invariants hold for the arguments; the block
    // touches no stack.
    unsafe {
        asm!(
            "ecall",
            in("a7") number.into_raw(),
            inlateout("a0") first.into_raw() => answer,
            in("a1") second.into_raw(),
            options(nostack, preserves_flags),
        );
    }
    Answer::from_raw(answer)
}

/// Issue system call `number` with four arguments, which writes no memory
/// of the process.
///
/// # Specification
/// - ensures: the kernel's answer.
/// - panics: none.
/// - executable: none — the call's effect is the kernel's.
///
/// # Safety
/// - unsafe invariants: each pointer argument names memory that is valid for
///   the call's reads, and the call writes no memory of the process.
///
/// # Adequacy
/// - hypothesis: L3 — buffers registered through this call carry a fixed write
///   and read.
/// - witness: `tests::io::a_registered_buffer_carries_a_fixed_write_and_read`
#[inline]
pub unsafe fn call4_readonly(
    number: Number,
    first: Argument<'_, First>,
    second: Argument<'_, Second>,
    third: Argument<'_, Third>,
    fourth: Argument<'_, Fourth>,
) -> Answer
{
    let answer;
    // SAFETY: as above; the caller's invariant lets the block promise that
    // it writes no memory.
    unsafe {
        asm!(
            "ecall",
            in("a7") number.into_raw(),
            inlateout("a0") first.into_raw() => answer,
            in("a1") second.into_raw(),
            in("a2") third.into_raw(),
            in("a3") fourth.into_raw(),
            options(nostack, preserves_flags, readonly),
        );
    }
    Answer::from_raw(answer)
}

/// Issue system call `number` with six arguments.
///
/// # Specification
/// - ensures: the kernel's answer.
/// - panics: none.
/// - executable: none — the call's effect is the kernel's.
///
/// # Safety
/// - unsafe invariants: each pointer argument names memory that is valid for
///   the call's access, and the caller allows each effect of the call.
///
/// # Adequacy
/// - hypothesis: L3 — queues mapped and entered through this call complete a
///   linked write, sync and read in order.
/// - witness: `tests::io::a_linked_write_sync_and_read_complete_in_order`
#[inline]
pub unsafe fn call6(
    number: Number,
    first: Argument<'_, First>,
    second: Argument<'_, Second>,
    third: Argument<'_, Third>,
    fourth: Argument<'_, Fourth>,
    fifth: Argument<'_, Fifth>,
    sixth: Argument<'_, Sixth>,
) -> Answer
{
    let answer;
    // SAFETY: the caller's invariants hold for the arguments; the block
    // touches no stack.
    unsafe {
        asm!(
            "ecall",
            in("a7") number.into_raw(),
            inlateout("a0") first.into_raw() => answer,
            in("a1") second.into_raw(),
            in("a2") third.into_raw(),
            in("a3") fourth.into_raw(),
            in("a4") fifth.into_raw(),
            in("a5") sixth.into_raw(),
            options(nostack, preserves_flags),
        );
    }
    Answer::from_raw(answer)
}
