//! The integration tests of `gandr-surface-render-terminal`: one target, each
//! area its own `cfg(test)` module, so a witness path reads
//! `tests::<area>::<name>`.

extern crate alloc;

#[cfg(test)]
mod corpus;
#[cfg(test)]
mod render;
