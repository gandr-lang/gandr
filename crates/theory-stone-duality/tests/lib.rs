//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::free::…`) instead of a file.

#[cfg(test)]
mod finite;
#[cfg(test)]
mod free;
