//! The integration tests of `gandr-surface-diagnostics`: one target, each area
//! its own `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

extern crate alloc;

#[cfg(test)]
mod diagnostics;
