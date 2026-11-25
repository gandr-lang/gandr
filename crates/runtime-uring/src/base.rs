//! The owner's system-call base: the kernel's `io_uring` interface with no C
//! library.
//!
//! The base issues `io_uring_setup`, `io_uring_register` and `io_uring_enter`
//! through inline assembly on five architectures. It holds the kernel's UAPI
//! declarations of six architectures, as the build script makes them, and the
//! four sizes of the ring's entries.
//!
//! The ring of this crate stands on the liburing crate, and no call of the
//! ring goes through the base yet.

#[cfg(not(target_os = "linux"))]
compile_error!("This crate is not supported on the target OS.");

#[cfg(not(any(
    any(target_arch = "aarch64", target_arch = "arm"),
    target_arch = "loongarch64",
    any(target_arch = "powerpc", target_arch = "powerpc64"),
    target_arch = "riscv64",
    target_arch = "s390x",
    any(target_arch = "x86", target_arch = "x86_64"),
)))]
compile_error!("This crate is not supported on the target architecture.");

mod io;
mod io_uring;
mod sys;

use crate::base::sys::linux::uapi::arch;
pub use crate::base::sys::linux::uapi::io_uring::io_uring_enter;
pub use crate::base::sys::linux::uapi::io_uring::io_uring_register;
pub use crate::base::sys::linux::uapi::io_uring::io_uring_register_with;
pub use crate::base::sys::linux::uapi::io_uring::io_uring_setup;

/// A submission entry of 64 bytes: the kernel's `io_uring_sqe`.
#[repr(transparent)]
pub struct Sqe64
{
    /// The kernel's entry.
    sqe: self::arch::io_uring_sqe,
}

/// A submission entry of 128 bytes: the kernel's entry and the 64 bytes that
/// a ring with `IORING_SETUP_SQE128` adds.
#[repr(C)]
pub struct Sqe128
{
    /// The kernel's entry.
    sqe: self::arch::io_uring_sqe,
    /// The bytes that the larger entry adds.
    pad: [u8; 64],
}

/// A completion entry of 16 bytes: the kernel's `io_uring_cqe`.
#[repr(transparent)]
#[non_exhaustive]
pub struct Cqe16
{
    /// The kernel's entry.
    cqe: self::arch::io_uring_cqe,
}

/// A completion entry of 32 bytes: the kernel's entry and the 16 bytes that a
/// ring with `IORING_SETUP_CQE32` adds.
#[repr(C)]
#[non_exhaustive]
pub struct Cqe32
{
    /// The kernel's entry.
    cqe: self::arch::io_uring_cqe,
    /// The bytes that the larger entry adds.
    pad: [u8; 16],
}

#[cfg(test)]
mod test
{
    use super::*;

    mod sqe
    {
        use super::*;

        mod sqe64
        {
            use super::*;

            #[test]
            fn size_of()
            {
                ::static_assertions_next::assert_size_eq!(Sqe64, [u8; 64]);
            }
        }

        mod sqe128
        {
            use super::*;

            #[test]
            fn size_of()
            {
                ::static_assertions_next::assert_size_eq!(Sqe128, [u8; 128]);
            }
        }
    }

    mod cqe
    {
        use super::*;

        mod cqe16
        {
            use super::*;

            #[test]
            fn size_of()
            {
                ::static_assertions_next::assert_size_eq!(Cqe16, [u8; 16]);
            }
        }

        mod cqe32
        {
            use super::*;

            #[test]
            fn size_of()
            {
                ::static_assertions_next::assert_size_eq!(Cqe32, [u8; 32]);
            }
        }
    }
}
