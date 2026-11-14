//! The IO layer of the storage tier: one `Io` for each worker, on the
//! kernel's own system calls, with no C library.
//!
//! A buffer moves into each submission and comes back with its completion,
//! one completion for each submission, keyed by its `Pending`. The `Io`
//! runs on an `io_uring` where the kernel gives one. Where the kernel
//! refuses one, it runs the same interface by positioned calls on the
//! caller's own thread, and `Io::form` reports which. A buffer lives in
//! the allocator that the caller names. `Io::with_faults` draws torn,
//! lost, misdirected and corrupt IO from a seed under each form.
//!
//! The layer moves bytes and checks no record: the store's plane reads the
//! header of each record that a read gives back, and refuses a record of
//! another place.
//!
//! The UAPI comes from the pinned kernel by `mise run uapi:generate`, and
//! the gate's `check:uapi` keeps it current. The layouts are the same on
//! each 64-bit Linux architecture. The crate issues its system calls by the
//! architecture's own instruction on Linux on x86-64, aarch64 and riscv64.
//! On any other target the crate holds the module `absent` alone, which
//! states the absence. So this lead names each item in code and links none:
//! a link resolves on one set of targets alone.
//!
//! # Items
//!
//! | Module | What it holds |
//! | ------ | ------------- |
//! | `uapi` | The `io_uring` layouts and the table of system-call numbers for x86-64, riscv64, aarch64, loongarch64, powerpc64 and s390x. `mise run uapi:generate` writes it from the pinned kernel, and the gate's `check:uapi` refuses a file that differs. |
//! | `sys` | `io_uring_setup`, `io_uring_enter`, `io_uring_register`, `mmap` and `munmap` on x86-64, aarch64 and riscv64. Each argument goes in a register of its own type, so a pointer keeps its provenance (`sys::registers`, `sys/arch/`). |
//! | `ring` | The mapped submission and completion queues. It stages entries, submits them and reads each completion once. It registers the ring's tables of fixed buffers and fixed files. |
//! | `io` | The completion contract. A buffer moves into each submission and comes back with its completion, keyed by the submission. `append` owns a segment's end. A full queue parks the caller until a submission completes. |
//! | `blocking` | The blocking form. The kernel can refuse the ring with `EPERM` or `ENOSYS`, or give a ring without stable submissions. Then the worker's own thread runs positioned calls behind the same interface. |
//! | `buffer` | The buffer in the allocator that the caller names, such as a worker's region. `Io::register` fixes buffers within the process's limit of locked memory, which the first registration reads, and says how many it fixes. The rest run unregistered. An allocator that refuses the bytes refuses the registration by the budget. |
//! | `faults` | The simulator of faults: torn, lost, misdirected and corrupt IO, drawn from a seed, the same under each form. An `Io` without it draws nothing. |
//!
//! A submission carries a key, and its completion carries the key back. An
//! entry linked to the next one starts the next only when it succeeds. The
//! kernel cancels the next one when it fails. A sync is `fdatasync`, as the
//! store's segment syncs.

/// The target holds no ring of the IO layer.
///
/// The crate's items stand on Linux on x86-64, aarch64 and riscv64 alone,
/// where the crate issues each system call by the architecture's own
/// instruction. A target outside that set, as macOS, holds this module
/// alone. powerpc64 and s390x have no entries yet, so they hold it too.
#[cfg(not(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
)))]
pub mod absent
{}

#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
extern crate alloc;

#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
mod blocking;
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
mod buffer;
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
mod faults;
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
mod io;
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
mod ring;
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
mod sys;
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
mod uapi;

#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
pub use crate::buffer::Buffer;
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
pub use crate::buffer::Fill;
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
pub use crate::faults::Fault;
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
pub use crate::faults::Odds;
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
pub use crate::faults::Seed;
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
pub use crate::io::Chain;
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
pub use crate::io::Done;
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
pub use crate::io::FILES;
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
pub use crate::io::Form;
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
pub use crate::io::Handle;
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
pub use crate::io::Io;
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
pub use crate::io::Pending;
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
pub use crate::io::Pinning;
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
pub use crate::io::Reason;
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
pub use crate::io::Refused;
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
pub use crate::io::Registered;
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
pub use crate::io::Segment;
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
pub use crate::ring::Count;
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
pub use crate::ring::Moved;
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
pub use crate::ring::Position;
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
pub use crate::sys::Errno;
