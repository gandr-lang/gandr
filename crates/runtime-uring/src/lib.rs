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

#[cfg(not(target_os = "linux"))]
compile_error!("This crate is only supported on Linux");

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
pub use crate::registrar::Registrar;
pub use crate::ring::IoUring;
pub use crate::ring::IoUringBuilder;
pub use crate::sqe::repr::Sqe64;
pub use crate::sqe::repr::Sqe128;
pub use crate::squeue::SubmissionQueue;
