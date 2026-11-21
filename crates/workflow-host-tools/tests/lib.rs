//! The integration tests of `gandr-workflow-host-tools`: one target, each
//! area its own `cfg(test)` module, so a witness path reads
//! `tests::<area>::<name>`.

#[cfg(test)]
mod cli;
