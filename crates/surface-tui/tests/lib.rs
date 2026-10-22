//! The integration tests of `gandr-surface-tui`: one target, each area its own
//! `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

extern crate alloc;

#[cfg(test)]
mod launch;
#[cfg(test)]
mod terminal;
