//! **Outputs**: the values that a program computes from the tree and that the
//! tree does not hold. A store outside the tree holds each value by the
//! digest of its tool and its input, so a run computes each value one time.
//!
//! - [`recovery`] writes the recovery record of a corpus source.
//! - [`roles`] writes the roles that the highlight gives a corpus source.
//! - [`store`] holds each value in one file, named by its key.
//! - [`tree`] reads a tree of the repository from git: its sources and the tool
//!   of a kind.
//! - [`workspace`] gives the packages that build a package.
//! - [`compute`] gives the values of one kind for a tree, from the store or
//!   computed by the writer of the kind.
//! - [`checkout`] computes the values of a commit by the binary of that commit,
//!   when its tool is not the tool of the run.
//! - [`difference`] gives the changes of the values between two trees.
//! - [`word`] reads the trailer with which a commit names the kinds whose
//!   values it changes.
//! - [`gauge`] watches the size of the store and the values that a run computes
//!   again, each with its bound and its event.
//!
//! The recovery sweep of `gandr-surface-parser` compares the record of each
//! source with this writer's record, so the sweep and the store cannot hold
//! two different records.

extern crate alloc;

pub mod checkout;
pub mod compute;
pub mod difference;
pub mod gauge;
pub mod recovery;
pub mod roles;
pub mod store;
pub mod tree;
pub mod word;
pub mod workspace;

pub use recovery::RecordError;
pub use recovery::Recorder;
