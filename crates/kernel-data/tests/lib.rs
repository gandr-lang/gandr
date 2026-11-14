//! The integration tests of `gandr-kernel-data`: one target, each area its
//! own `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

#[cfg(test)]
mod region;
