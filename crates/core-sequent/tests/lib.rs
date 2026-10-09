//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::csl_fibration::…`) instead of a file.

extern crate alloc;

#[cfg(test)]
mod csl_fibration;
