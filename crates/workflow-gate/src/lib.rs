//! The inputs of a check of a landing's gate, and their digest, for each
//! check and each commit in one run.
//!
//! A verdict is a function of what its check reads. So a record of the
//! verdict binds the digest of those inputs, and a gate asks for that digest
//! at its head and at its base, for each long check. A run for each digest
//! starts Cargo, mise and git again each time. This crate answers for each
//! check and each commit in one run, and it does each piece of work one
//! time.
//!
//! # Items
//!
//! - [`lists`] gives the list of the inputs of each check of a [`Request`] at
//!   each of its commits, as a [`Listed`].
//! - [`List`] is the inputs of one check at one commit, and its [`Digest`] is
//!   the name that a record binds.
//! - [`keys`] gives the [`Key`] of the verdict of each check of a
//!   [`KeyRequest`]: each input that the verdict reads, as one line.
//! - [`Parts`] holds the count and the time of each call of a run, and
//!   [`Elapsed`] writes a time.
//! - [`GateError`] is each refusal of a run.
//!
//! # Boundaries
//!
//! One run reads the crates from `cargo metadata` one time and the tasks
//! from `mise tasks ls` one time. It asks git for each object one time in
//! one batch, and it runs `git grep` one time for each distinct tree that a
//! grep reads. The programs that do not wait for each other run at the same
//! time. The crates are those of the worktree for each commit, as Cargo reads
//! them there.

extern crate alloc;

mod call;
mod error;
mod list;
mod name;
mod run;
mod tables;
mod verdict;

pub use crate::call::Elapsed;
pub use crate::call::Parts;
pub use crate::error::GateError;
pub use crate::list::Digest;
pub use crate::list::List;
pub use crate::list::Listed;
pub use crate::name::Check;
pub use crate::name::Commit;
pub use crate::name::Scope;
pub use crate::run::Request;
pub use crate::run::lists;
pub use crate::verdict::Key;
pub use crate::verdict::KeyRequest;
pub use crate::verdict::keys;
