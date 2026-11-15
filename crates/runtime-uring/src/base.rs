#![cfg_attr(
    test,
    allow(
        clippy::as_conversions,
        clippy::indexing_slicing,
        clippy::items_after_statements,
        clippy::let_unit_value,
        clippy::panic_in_result_fn,
        clippy::too_many_arguments,
        clippy::unwrap_used,
        clippy::undocumented_unsafe_blocks,
        reason = "cfg(test)"
    )
)]
#![allow(clippy::missing_docs_in_private_items, reason = "WIP")]
#![allow(clippy::missing_safety_doc, reason = "WIP")]
// #![allow(unused, reason = "WIP")]

// Features
#![cfg_attr(asm_experimental_arch, feature(asm_experimental_arch))]

//! TODO

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

extern crate alloc;

mod io;
mod io_uring;
mod sys;

use crate::base::sys::linux::uapi::arch;
pub use crate::base::sys::linux::uapi::io_uring::io_uring_enter;
pub use crate::base::sys::linux::uapi::io_uring::io_uring_register;
pub use crate::base::sys::linux::uapi::io_uring::io_uring_register_with;
pub use crate::base::sys::linux::uapi::io_uring::io_uring_setup;

#[repr(transparent)]
pub struct Sqe64
{
    sqe: self::arch::io_uring_sqe,
}

#[repr(C)]
pub struct Sqe128
{
    sqe: self::arch::io_uring_sqe,
    pad: [u8; 64],
}

#[repr(transparent)]
#[non_exhaustive]
pub struct Cqe16
{
    cqe: self::arch::io_uring_cqe,
}

#[repr(C)]
#[non_exhaustive]
pub struct Cqe32
{
    cqe: self::arch::io_uring_cqe,
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
