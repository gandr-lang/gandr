//! The system call instruction of x86-64. The number goes in `rax`, and the
//! arguments go in `rdi`, `rsi`, `rdx`, `r10`, `r8` and `r9`. The answer comes
//! back in `rax`, and the instruction overwrites `rcx` and `r11`.

use core::arch::asm;

use super::Call;
use super::Raw;

/// The number of `mmap` on x86-64.
pub(super) const MMAP: Call = Call(9);

/// The number of `mprotect` on x86-64.
pub(super) const MPROTECT: Call = Call(10);

/// The number of `munmap` on x86-64.
pub(super) const MUNMAP: Call = Call(11);

/// Issues the system call `call` with six arguments.
///
/// # Safety
///
/// - unsafe invariants: each argument is what the call takes, and the caller
///   allows each effect of the call.
///
/// # Specification
///
/// - ensures: the kernel's answer, unread.
/// - panics: none.
/// - executable: none — the call's effect is the kernel's.
///
/// # Adequacy
///
/// - hypothesis: L3 — a page that `map` gives takes a byte, and `unmap` gives
///   it back.
/// - witness: `tests::map::a_block_takes_a_byte_on_each_page`
#[inline]
pub(super) unsafe fn syscall6(
    call: Call,
    arguments: [Raw; 6],
) -> Raw
{
    let answer: usize;
    // SAFETY: the caller's invariants hold for the arguments, and the block
    // declares each register that the instruction overwrites and touches no
    // stack.
    unsafe {
        asm!(
            "syscall",
            inlateout("rax") call.0 => answer,
            in("rdi") arguments[0].0,
            in("rsi") arguments[1].0,
            in("rdx") arguments[2].0,
            in("r10") arguments[3].0,
            in("r8") arguments[4].0,
            in("r9") arguments[5].0,
            lateout("rcx") _,
            lateout("r11") _,
            options(nostack, preserves_flags)
        );
    }
    Raw(answer)
}
