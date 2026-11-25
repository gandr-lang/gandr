//! The integration tests of `gandr-workflow-prose`: one target, each area its
//! own `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

#[cfg(test)]
mod cli;
