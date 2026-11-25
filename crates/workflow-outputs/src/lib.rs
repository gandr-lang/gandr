//! **Outputs**: the values that a program computes from the tree and that the
//! tree does not hold. Each kind of output has a writer of one value for each
//! input.
//!
//! - [`recovery`] writes the recovery record of a corpus source.
//!
//! The recovery sweep of `gandr-surface-parser` compares the record of each
//! source with this writer's record, so the sweep and the writer cannot name
//! two different records.

pub mod recovery;

pub use recovery::RecordError;
pub use recovery::Recorder;
