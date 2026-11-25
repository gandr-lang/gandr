//! The system call instruction of x86-64. The number goes in `rax`, and the
//! arguments go in `rdi`, `rsi`, `rdx` and `r10`. The answer comes back in
//! `rax`, and the instruction overwrites `rcx` and `r11`.

use core::arch::asm;

use super::Call;
use super::Raw;

/// The number of `read` on x86-64.
pub(super) const READ: Call = Call(0);

/// The number of `close` on x86-64.
pub(super) const CLOSE: Call = Call(3);

/// The number of `openat` on x86-64.
pub(super) const OPENAT: Call = Call(257);

/// Issues the system call `call` with four arguments.
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
/// - hypothesis: L3 — a file of the tree opens, reads whole and closes.
/// - witness: `tests::file::a_file_of_the_tree_reads_whole_in_steps_of_one_page`
#[inline]
pub(super) unsafe fn syscall4(
    call: Call,
    arguments: [Raw; 4],
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
            lateout("rcx") _,
            lateout("r11") _,
            options(nostack, preserves_flags)
        );
    }
    Raw(answer)
}
