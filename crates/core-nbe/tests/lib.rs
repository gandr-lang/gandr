//! The integration tests of `gandr-core-nbe`: one target, each area its own
//! `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

extern crate alloc;

/// The expansion oracle, shared with the measure's suite.
#[cfg(test)]
#[path = "support/unfolding.rs"]
mod unfolding;

/// The tree oracle, shared with the duplication suite.
#[cfg(test)]
#[path = "support/trees.rs"]
mod trees;

#[cfg(test)]
mod deep_evaluation;
#[cfg(test)]
mod deep_readback;
#[cfg(test)]
mod duplication;
#[cfg(test)]
mod full_laziness;
#[cfg(test)]
mod glued_shape;
#[cfg(test)]
mod measure;
#[cfg(test)]
mod readback_terms;
#[cfg(test)]
mod static_normalization;
#[cfg(test)]
mod teardown;
