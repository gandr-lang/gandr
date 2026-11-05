//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::laws::…`) instead of a file.

#[cfg(test)]
mod laws;
