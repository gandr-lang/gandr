//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a contract's witness path names the
//! area it belongs to (`tests::incremental::…`) instead of a file.

extern crate alloc;

#[cfg(test)]
mod common;
#[cfg(test)]
mod generate;

#[cfg(test)]
mod defects;
#[cfg(test)]
mod incremental;
