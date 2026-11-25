//! The system call instruction of riscv64. The number goes in `a7`, and the
//! arguments go in `a0` to `a3`. The answer comes back in `a0`. The numbers
//! are the generic table of Linux, which riscv64 uses.

use core::arch::asm;

use super::Call;
use super::Raw;

/// The number of `read` on riscv64.
pub(super) const READ: Call = Call(63);

/// The number of `write` on riscv64.
pub(super) const WRITE: Call = Call(64);

/// The number of `close` on riscv64.
pub(super) const CLOSE: Call = Call(57);

/// The number of `openat` on riscv64.
pub(super) const OPENAT: Call = Call(56);

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
            "ecall",
            in("a7") call.0,
            inlateout("a0") arguments[0].0 => answer,
            in("a1") arguments[1].0,
            in("a2") arguments[2].0,
            in("a3") arguments[3].0,
            options(nostack, preserves_flags)
        );
    }
    Raw(answer)
}
