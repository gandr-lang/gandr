//! The integration tests of `gandr-theory-discrete-morse`: one target, each
//! area its own `cfg(test)` module, so a witness path reads
//! `tests::<area>::<name>`.
//!
//! The face posets of the corpus shapes are the graded posets crate's test
//! fixture, read here from its one file.

extern crate alloc;

#[cfg(test)]
mod collapse;
#[cfg(test)]
mod complex;
#[cfg(test)]
mod euler;
#[cfg(test)]
#[path = "../../theory-graded-posets/tests/faces.rs"]
mod faces;
#[cfg(test)]
mod greedy;
#[cfg(test)]
mod poset;
#[cfg(test)]
mod reduct;
#[cfg(test)]
mod simplices;
