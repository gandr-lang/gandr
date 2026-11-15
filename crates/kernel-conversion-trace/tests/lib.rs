//! The integration tests of `gandr-kernel-conversion-trace`: one target, each
//! area its own `cfg(test)` module, so a witness path reads
//! `tests::<area>::<name>`.

#[cfg(test)]
mod differential;
