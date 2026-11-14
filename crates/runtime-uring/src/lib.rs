//! The kernel's `io_uring`: the ring, its submission and completion queues,
//! its registrar of files, and a preparer for each operation that liburing
//! names.
//!
//! [`IoUring`] sets up a ring through [`IoUringBuilder`], which takes each
//! setup flag at most once and fixes the sizes of the two kinds of entry in
//! the ring's type. [`SubmissionQueue`] gives free entries; each preparer is
//! a method of [`Sqe64`] in the module [`sqe`] that names its operation.
//! [`CompletionQueue`] gives the ready completions, or waits for them, and
//! marks each given one as seen when its run drops.
//!
//! The crate stands on liburing, the kernel's C library of the ring, as the
//! owner's crate does. On a system other than Linux it compiles empty.

// The ring is the Linux kernel's: on another system the crate compiles empty.
#![cfg(target_os = "linux")]
// The owner's text as it stands meets the wall at these sites; the rule of
// the port forbids a rewrite, and #7645 owes a mend in place for each:
// 347 preparer arguments of the kernel's C types, 16 fields that the ring's
// modules read across modules, 15 counters, 8 references made raw by
// coercion, and 38 structs that the builder's macro makes.
#![expect(
    clippy::arithmetic_side_effects,
    clippy::field_scoped_visibility_modifiers,
    reason = "the owner's text, kept as it stands; #7645 owes each mend in place"
)]
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        primitive_signature,
        raw_pointer_through_reference,
        single_field_struct_needs_transparent_repr,
        reason = "the owner's text, kept as it stands; #7645 owes each mend in place"
    )
)]
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
