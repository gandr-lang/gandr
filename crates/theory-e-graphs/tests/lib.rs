//! The integration tests of `gandr-theory-e-graphs`: one target, each area
//! its own `cfg(test)` module, so a witness path reads
//! `tests::<area>::<name>`.

extern crate alloc;

#[cfg(test)]
mod analysis;
#[cfg(test)]
mod explain;
#[cfg(test)]
mod fixtures;
#[cfg(test)]
mod graph;
#[cfg(test)]
mod phases;
