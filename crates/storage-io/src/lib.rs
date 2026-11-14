//! The IO layer of the storage tier: one `io_uring` for each worker, on the
//! kernel's own system calls, with no C library.
//!
//! The UAPI comes from the pinned kernel by `mise run uapi:generate`, and
//! the gate's `check:uapi` keeps it current. The layouts are the same on
//! each 64-bit Linux architecture. The crate issues its system calls by the
//! architecture's own instruction on x86-64 and riscv64; on any other target
//! it holds no ring.

#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "riscv64")
))]
mod ring;
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "riscv64")
))]
mod sys;
#[cfg(target_os = "linux")]
mod uapi;

#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "riscv64")
))]
pub use crate::ring::Buffer;
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "riscv64")
))]
pub use crate::ring::Completion;
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "riscv64")
))]
pub use crate::ring::Count;
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "riscv64")
))]
pub use crate::ring::Entry;
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "riscv64")
))]
pub use crate::ring::Full;
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "riscv64")
))]
pub use crate::ring::Key;
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "riscv64")
))]
pub use crate::ring::Moved;
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "riscv64")
))]
pub use crate::ring::Position;
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "riscv64")
))]
pub use crate::ring::Ring;
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "riscv64")
))]
pub use crate::sys::Errno;
