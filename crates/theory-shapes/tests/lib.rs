//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::finite::…`) instead of a file.

extern crate alloc;

#[cfg(test)]
mod carriers;
#[cfg(test)]
mod errors;
#[cfg(test)]
mod faces;
#[cfg(test)]
mod finite;
