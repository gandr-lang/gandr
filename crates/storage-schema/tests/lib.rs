//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a contract's witness path names the
//! area it belongs to (`tests::defect::…`) instead of a file.

#[cfg(test)]
mod common;

#[cfg(test)]
mod defect;
#[cfg(test)]
mod equations;
#[cfg(test)]
mod keyed;
#[cfg(test)]
mod migrate;
#[cfg(test)]
mod proofs;
#[cfg(test)]
mod render;
#[cfg(test)]
mod schema;
