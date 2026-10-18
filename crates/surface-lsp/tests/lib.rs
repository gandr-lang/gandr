//! The integration tests of `gandr-surface-lsp`: one target, each area its own
//! `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

extern crate alloc;

#[cfg(test)]
mod capabilities;
#[cfg(test)]
mod editor;
#[cfg(test)]
mod session;
