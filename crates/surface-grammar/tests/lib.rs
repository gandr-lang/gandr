//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a contract's witness path names the
//! area it belongs to (`tests::pbg::…`) instead of a file.

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(linear_search_in_loop, reason = "6 cost-shape sites; #814 lists them")
)]

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
mod spelling;
#[cfg(test)]
mod surface;
#[cfg(test)]
mod walk;
