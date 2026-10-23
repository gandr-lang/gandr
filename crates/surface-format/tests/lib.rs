//! The integration tests of `gandr-surface-format`: one target, each area its
//! own `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

extern crate alloc;

#[cfg(test)]
mod attach;

#[cfg(test)]
mod format;

#[cfg(test)]
mod rewrite;
