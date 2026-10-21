//! **Build state**: a Cargo profile directory pruned to the units the
//! recorded builds used, so the state CI carries from landing to landing
//! stays the size of one build.
//!
//! Cargo names every file a unit writes with a hash of the unit's package,
//! features, profile and dependencies. An edit rebuilds a unit under the
//! same hash; a changed dependency, feature or lockfile entry writes the
//! unit and everything above it under new hashes, and Cargo never deletes
//! the superseded ones. A target directory restored, rebuilt and saved
//! again on every landing grows with every manifest change.
//!
//! - [`units`] reads the JSON messages a build prints, fresh units included,
//!   into the set of units it used.
//! - [`mod@prune`] removes every hashed entry of the profile directory's
//!   `deps`, `build`, `.fingerprint` and `examples` that no recorded unit
//!   names, and finds the unit behind each executable Cargo copied out under
//!   its plain name by the hard link between the two.
//!
//! # Boundaries
//!
//! The keep set is the units the build's JSON messages name, fresh units
//! included. A prune refuses a message file that lacks Cargo's successful
//! `build-finished` message, so a partial account never deletes a unit the
//! build needs.
//!
//! # References
//!
//! See the [crate README](https://github.com/gandr-lang/gandr/blob/main/crates/workflow-build-state/README.md).

pub mod error;
pub mod prune;
pub mod units;

pub use crate::error::BuildStateError;
pub use crate::prune::Pruned;
pub use crate::prune::prune;
pub use crate::units::Messages;
pub use crate::units::UnitHash;
pub use crate::units::Units;
