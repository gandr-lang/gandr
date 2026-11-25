//! **Outputs**: the values that a program computes from the tree and that the
//! tree does not hold. A store outside the tree holds each value by the
//! digest of its tool and its input, so a run computes each value one time.
//!
//! - [`recovery`] writes the recovery record of a corpus source.
//! - [`store`] holds each value in one file, named by its key.
//! - [`tree`] reads a tree of the repository from git: its sources and the tool
//!   of a kind.
//! - [`workspace`] gives the packages that build a package.
//! - [`compute`] gives the values of a tree, from the store or computed.
//!
//! The recovery sweep of `gandr-surface-parser` compares the record of each
//! source with this writer's record, so the sweep and the store cannot hold
//! two different records.

extern crate alloc;

pub mod compute;
pub mod recovery;
pub mod store;
pub mod tree;
pub mod workspace;

pub use recovery::RecordError;
pub use recovery::Recorder;
