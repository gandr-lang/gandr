//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a contract's witness path names the
//! area it belongs to (`tests::pbg::…`) instead of a file.

extern crate alloc;

#[cfg(test)]
mod closing_class;
#[cfg(test)]
mod highlight;
#[cfg(test)]
mod pbg;
#[cfg(test)]
mod regex;
#[cfg(test)]
mod surface;
#[cfg(test)]
mod walk;
