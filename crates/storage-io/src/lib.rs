//! The IO layer of the storage tier: one [`Io`] for each worker, on the
//! kernel's own system calls, with no C library.
//!
//! A buffer moves into each submission and comes back with its completion,
//! one completion for each submission, keyed by its [`Pending`]. The `Io`
//! runs on an `io_uring` where the kernel gives one. Where the kernel
//! refuses one, it runs the same interface on one thread of positioned
//! calls, and [`Io::form`] reports which.
//!
//! The UAPI comes from the pinned kernel by `mise run uapi:generate`, and
//! the gate's `check:uapi` keeps it current. The layouts are the same on
//! each 64-bit Linux architecture. The crate issues its system calls by the
//! architecture's own instruction on x86-64 and riscv64; on any other target
//! it holds no ring.

extern crate alloc;

#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "riscv64")
))]
mod blocking;
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "riscv64")
))]
mod buffer;
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "riscv64")
))]
mod io;
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
pub use crate::buffer::Buffer;
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "riscv64")
))]
pub use crate::io::Chain;
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "riscv64")
))]
pub use crate::io::Done;
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "riscv64")
))]
pub use crate::io::Form;
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "riscv64")
))]
pub use crate::io::Handle;
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "riscv64")
))]
pub use crate::io::Io;
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "riscv64")
))]
pub use crate::io::Pending;
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "riscv64")
))]
pub use crate::io::Reason;
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "riscv64")
))]
pub use crate::io::Refused;
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "riscv64")
))]
pub use crate::io::Segment;
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "riscv64")
))]
pub use crate::ring::Count;
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
pub use crate::sys::Errno;
