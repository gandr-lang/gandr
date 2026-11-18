//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::run::…`) instead of a file.

extern crate alloc;

#[cfg(test)]
mod closures;
#[cfg(test)]
mod compare;
#[cfg(test)]
mod differential;
#[cfg(test)]
mod focus_properties;
#[cfg(test)]
mod generate;
#[cfg(test)]
mod refusals;
#[cfg(test)]
mod run;
