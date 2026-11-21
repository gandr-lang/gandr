//! The system call instruction of riscv64. The number goes in `a7`, and the
//! arguments go in `a0` to `a5`. The answer comes back in `a0`.

use core::arch::asm;

use super::Call;
use super::Raw;

/// The number of `mmap` on riscv64.
pub(super) const MMAP: Call = Call(222);

/// The number of `mprotect` on riscv64.
pub(super) const MPROTECT: Call = Call(226);

/// The number of `munmap` on riscv64.
pub(super) const MUNMAP: Call = Call(215);

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
            "ecall",
            in("a7") call.0,
            inlateout("a0") arguments[0].0 => answer,
            in("a1") arguments[1].0,
            in("a2") arguments[2].0,
            in("a3") arguments[3].0,
            in("a4") arguments[4].0,
            in("a5") arguments[5].0,
            options(nostack, preserves_flags)
        );
    }
    Raw(answer)
}
