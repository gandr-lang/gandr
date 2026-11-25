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
//! - [`read`] gives the [`Reading`] of a [`ReadRequest`]: which check holds on
//!   a tree, by the inputs of its base or by a signed record of a pass, with
//!   one line for each fact and an [`End`].
//! - [`write()`] signs one record of a [`WriteRequest`] for the checks of a
//!   gate, and [`send`] pushes the records of a tree for a [`SendRequest`].
//! - [`tree`] gives the tree of the work. [`record()`] writes the pass of a
//!   gate on a tree, [`require`] answers whether a gate passed on a head, and
//!   [`admit`] writes here the pass of a gate on another host. [`times`] and
//!   [`passed`] are their rules.
//! - [`Parts`] holds the count and the time of each call of a run, [`Part`]
//!   names one, and [`Elapsed`] writes a time.
//! - [`scope()`] gives the [`Scoped`] of a [`ScopeRequest`]: the crates that a
//!   change can break, each touched crate with each crate that depends on it.
//! - [`GateError`] is each refusal of a run.
//!
//! # Boundaries
//!
//! One run reads the crates from `cargo metadata` one time and the tasks
//! from `mise tasks ls` one time. It asks git for each object one time in
//! one batch, and it runs `git grep` one time for each distinct tree that a
//! grep reads. A read asks the remote two times at most, and verifies all
//! records with one `git verify-commit`. The programs that do not wait for
//! each other run at the same time. The crates are those of the worktree for
//! each commit, as Cargo reads them there.

extern crate alloc;

mod call;
mod error;
mod list;
mod name;
mod pass;
mod record;
mod run;
mod scope;
mod tables;
mod verdict;
mod write;

pub use crate::call::Elapsed;
pub use crate::call::Part;
pub use crate::call::Parts;
pub use crate::error::GateError;
pub use crate::list::Digest;
pub use crate::list::List;
pub use crate::list::Listed;
pub use crate::name::Check;
pub use crate::name::Commit;
pub use crate::name::Scope;
pub use crate::pass::AdmitRequest;
pub use crate::pass::Passed;
pub use crate::pass::Passing;
pub use crate::pass::RecordRequest;
pub use crate::pass::RequireRequest;
pub use crate::pass::Suite;
pub use crate::pass::TaskTime;
pub use crate::pass::TestTime;
pub use crate::pass::Timed;
pub use crate::pass::Times;
pub use crate::pass::admit;
pub use crate::pass::passed;
pub use crate::pass::record;
pub use crate::pass::require;
pub use crate::pass::stamp;
pub use crate::pass::times;
pub use crate::pass::tree;
pub use crate::record::End;
pub use crate::record::ReadRequest;
pub use crate::record::Reading;
pub use crate::record::read;
pub use crate::run::Request;
pub use crate::run::lists;
pub use crate::scope::ScopeRequest;
pub use crate::scope::Scoped;
pub use crate::scope::scope;
pub use crate::verdict::Key;
pub use crate::verdict::KeyRequest;
pub use crate::verdict::keys;
pub use crate::write::SendRequest;
pub use crate::write::WriteRequest;
pub use crate::write::send;
pub use crate::write::write;
