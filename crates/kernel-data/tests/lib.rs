//! The integration tests of `gandr-kernel-data`: one target, each area its
//! own `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

extern crate alloc;

#[cfg(test)]
mod region;

#[cfg(test)]
mod small_vec;
