//! The integration tests of `gandr-kernel-term`: one target, each area its own
//! `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

extern crate alloc;

#[cfg(test)]
mod adversarial_depth;
#[cfg(test)]
mod sharing_format;
