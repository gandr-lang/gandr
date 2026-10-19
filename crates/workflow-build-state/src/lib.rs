//! **Build state**: a Cargo profile directory pruned to the units the
//! recorded builds used, so the state CI carries from landing to landing
//! stays the size of one build.
//!
//! Cargo names every file a unit writes with a hash of the unit's package,
//! features, profile and dependencies. An edit rebuilds a unit under the
//! same hash; a changed dependency, feature or lockfile entry writes the
//! unit and everything above it under new hashes, and Cargo never deletes
//! the superseded ones. A target directory restored, rebuilt and saved
//! again on every landing therefore grows with every manifest change: the
//! enforcing test state held 763 test executables for 106 test targets,
//! 8.4 GB where one build is 1.5 GB.
//!
//! - [`units`] reads the JSON messages a build prints, fresh units included,
//!   into the set of units it used.
//! - [`mod@prune`] removes every hashed entry of the profile directory's
//!   `deps`, `build`, `.fingerprint` and `examples` that no recorded unit
//!   names, and finds the unit behind each executable Cargo copied out under
//!   its plain name by the hard link between the two.
//!
//! # Decisions
//!
//! **The keep set is Cargo's own account of the build.** The alternatives
//! lost on correctness: `cargo-sweep`'s timestamp mode keeps what was read
//! after a stamp, but a unit Cargo finds fresh is never read, so it would
//! delete exactly the restored state a warm build reuses (the crate is also
//! unmaintained); `cargo clean` before saving keeps nothing to reuse; and
//! keying the saved state on the manifests, the design this replaces,
//! discards every compiled dependency on any manifest edit. A prune
//! refuses a message file without Cargo's successful `build-finished`
//! message, so a partial account never deletes a unit the build needs.
//!
//! **Reversal**: Cargo collecting its own build directory's garbage (its
//! `gc` work covers only the shared download cache today), at which point
//! the directory is saved as the build left it.
//!
//! See the [crate README](https://github.com/gandr-lang/gandr/blob/main/crates/workflow-build-state/README.md).

// Module documentation that predates the shape lint: 1 heading outside the
// vocabulary and 1 decision record. Each allow leaves with the rewrite that
// clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        reason = "module documentation that predates the shape lint"
    )
)]
pub mod error;
pub mod prune;
pub mod units;

pub use crate::error::BuildStateError;
pub use crate::prune::Pruned;
pub use crate::prune::prune;
pub use crate::units::Messages;
pub use crate::units::UnitHash;
pub use crate::units::Units;
