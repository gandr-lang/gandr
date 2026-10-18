//! The integration tests of `gandr-workflow-spec-cost`: one target, each area
//! its own `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

#[cfg(test)]
mod cli;
#[cfg(test)]
mod ratio;
