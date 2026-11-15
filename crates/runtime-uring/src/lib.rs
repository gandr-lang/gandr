//! The kernel's `io_uring`: the ring, its submission and completion queues,
//! its registrar of files, and a preparer for each operation that liburing
//! names.
//!
//! `IoUring` sets up a ring through `IoUringBuilder`, which takes each setup
//! flag at most once and fixes the sizes of the two kinds of entry in the
//! ring's type. `SubmissionQueue` gives free entries; each preparer is a
//! method of `Sqe64` in the module `sqe` that names its operation.
//! `CompletionQueue` gives the ready completions, or waits for them, and
//! marks each given one as seen when its run drops.
//!
//! The ring stands on liburing, the kernel's C library of the ring, as the
//! owner's older crate does. The module `base` holds the owner's newer
//! system-call base beside it: `io_uring_setup`, `io_uring_register` and
//! `io_uring_enter` by inline assembly, the UAPI of six architectures and
//! the four sizes of entry. No call of the ring goes through the base yet.
//!
//! On a system other than Linux the crate compiles empty. So this lead names
//! each item in code and links none: a link resolves on Linux alone.
//!
//! # References
//!
//! - `vault:01a1d8c5-08cb-7e12-a5d5-9a2ad3279160` — anchor: the owner's crate,
//!   copied whole and mended in place, with its build script and the made
//!   declarations of each architecture.

// The ring is the Linux kernel's: on another system the crate compiles empty.
#![cfg(target_os = "linux")]
// The base's entries on powerpc64 use inline assembly, which is unstable on
// that architecture. The build script names the cfg that turns the feature on.
#![cfg_attr(asm_experimental_arch, feature(asm_experimental_arch))]

pub mod arg;
pub mod base;
pub mod cqe;
mod cqueue;
mod fd;
mod registrar;
mod ring;
pub mod sqe;
mod squeue;
pub(crate) mod sys;

pub use crate::cqe::repr::Cqe16;
pub use crate::cqe::repr::Cqe32;
pub use crate::cqueue::CompletionQueue;
pub use crate::fd::SlotDesc;
pub use crate::registrar::Registrar;
pub use crate::ring::IoUring;
pub use crate::ring::IoUringBuilder;
pub use crate::sqe::repr::Sqe64;
pub use crate::sqe::repr::Sqe128;
pub use crate::squeue::SubmissionQueue;
