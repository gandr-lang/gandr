//! The integration tests of `gandr-workflow-ledger-tasks`: one target, each
//! area its own `cfg(test)` module, so a witness path reads
//! `tests::<area>::<name>`. Each witness of a ledger's build is a unit test of
//! the `ledger` module that builds it; the `cli` cases run each verb of
//! `gandr-ledger` end to end.

#[cfg(test)]
mod cli;
