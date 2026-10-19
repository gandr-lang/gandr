//! The integration tests of `gandr-surface-dispatcher`: one target, each area
//! its own `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

extern crate alloc;

#[cfg(test)]
mod builtins;
#[cfg(test)]
mod census;
#[cfg(test)]
mod coincide;
#[cfg(test)]
mod corpus;
#[cfg(test)]
mod entries;
#[cfg(test)]
mod parity;
#[cfg(test)]
mod run;
