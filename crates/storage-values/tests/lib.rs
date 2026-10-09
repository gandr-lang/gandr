//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a contract's witness path names the
//! area it belongs to (`tests::values::…`) instead of a file.

extern crate alloc;

#[cfg(test)]
mod common;
#[cfg(test)]
mod generate;
#[cfg(test)]
mod reference;

#[cfg(test)]
mod flat;
#[cfg(test)]
mod frame;
#[cfg(test)]
mod laws;
#[cfg(test)]
mod values;
