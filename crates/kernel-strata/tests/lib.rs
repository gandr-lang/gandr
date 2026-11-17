//! The integration tests of `gandr-kernel-strata`: one target, each area its
//! own `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

extern crate alloc;

#[cfg(test)]
mod entailment_oracle;
#[cfg(test)]
mod level_oracle;
