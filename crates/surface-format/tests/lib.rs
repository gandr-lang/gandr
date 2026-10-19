//! The integration tests of `gandr-surface-format`: one target, each area its
//! own `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

#[cfg(test)]
mod attach;

#[cfg(test)]
mod format;
