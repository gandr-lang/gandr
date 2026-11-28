//! The integration tests of `gandr-workflow-tree-rules`: one target, each
//! area its own `cfg(test)` module, so a witness path reads
//! `tests::<area>::<name>`.

#[cfg(test)]
mod cases;
#[cfg(test)]
mod cli;
