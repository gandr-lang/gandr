//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::inhabitant::…`) instead of a file.

#[cfg(test)]
mod adversary;
#[cfg(test)]
mod inhabitant;
#[cfg(test)]
mod workspace;
