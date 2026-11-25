//! The system call instruction of aarch64. The number goes in `x8`, and the
//! arguments go in `x0` to `x5`. The answer comes back in `x0`.

use core::arch::asm;

use super::Call;
use super::Raw;

/// The number of `mmap` on aarch64.
pub(super) const MMAP: Call = Call(222);

/// The number of `mprotect` on aarch64.
pub(super) const MPROTECT: Call = Call(226);

/// The number of `munmap` on aarch64.
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
            "svc 0",
            in("x8") call.0,
            inlateout("x0") arguments[0].0 => answer,
            in("x1") arguments[1].0,
            in("x2") arguments[2].0,
            in("x3") arguments[3].0,
            in("x4") arguments[4].0,
            in("x5") arguments[5].0,
            options(nostack, preserves_flags)
        );
    }
    Raw(answer)
}
