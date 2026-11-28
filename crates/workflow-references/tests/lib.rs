//! The integration tests of `gandr-workflow-references`: one target, each
//! area its own `cfg(test)` module, so a witness path reads
//! `tests::<area>::<name>`.

extern crate alloc;

#[cfg(test)]
mod cites;
#[cfg(test)]
mod cli;
#[cfg(test)]
mod window;
