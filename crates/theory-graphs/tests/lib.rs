//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a contract's witness path names the
//! area it belongs to (`tests::prec::…`) instead of a file.

extern crate alloc;

#[cfg(test)]
mod algorithms;
#[cfg(test)]
mod prec;
#[cfg(test)]
mod walk;
