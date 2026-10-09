//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::code_iso::…`) instead of a file. The suites live here
//! rather than beside the code because they need `std`: the property runner,
//! shared closures, and the resolver query.

extern crate alloc;

#[cfg(test)]
mod code_iso;
#[cfg(test)]
mod support;
#[cfg(test)]
mod vdc_dictionary;
#[cfg(test)]
mod workspace;
