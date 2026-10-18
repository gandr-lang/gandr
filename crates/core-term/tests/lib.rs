//! The integration tests of `gandr-core-term`: one target, each area its own
//! `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

#[cfg(test)]
mod deep_static;
#[cfg(test)]
mod one_context;
