//! The integration tests of `gandr-workflow-twin-census`: one target, each
//! area its own `cfg(test)` module, so a witness path reads
//! `tests::<area>::<name>`.

#[cfg(test)]
mod census;
#[cfg(test)]
mod cli;
