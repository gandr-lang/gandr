//! Architecture-specific syscall code.
//!
//! This module also has a `strategy` alias which chooses a scheme and is
//! what the base's three calls use.
//!
//! Compilers should really have intrinsics for making system calls. They're
//! much like regular calls, with custom calling conventions, and calling
//! conventions are otherwise the compiler's job. But for now, use inline asm.
//!
//! The calling conventions for Linux syscalls are [documented here].
//!
//! [documented here]: https://man7.org/linux/man-pages/man2/syscall.2.html
//!
//! # Safety
//!
//! This contains the inline `asm` statements performing the syscall
//! instructions.

pub mod convert;
pub mod registers;

// These functions always use the machine's syscall instruction, even when it
// isn't the fastest option available.
#[cfg_attr(target_arch = "aarch64", path = "syscalls/arch/aarch64.rs")]
#[cfg_attr(target_arch = "powerpc64", path = "syscalls/arch/powerpc64.rs")]
#[cfg_attr(target_arch = "riscv64", path = "syscalls/arch/riscv64.rs")]
#[cfg_attr(target_arch = "s390x", path = "syscalls/arch/s390x.rs")]
#[cfg_attr(target_arch = "x86_64", path = "syscalls/arch/x86_64.rs")]
pub mod arch;

// On most architectures, the architecture syscall instruction is fast, so use
// it directly.
#[cfg(any(
    target_arch = "aarch64",
    target_arch = "powerpc64",
    target_arch = "riscv64",
    target_arch = "s390x",
    target_arch = "x86_64",
))]
pub use self::arch as strategy;
