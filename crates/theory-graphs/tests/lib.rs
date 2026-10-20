//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a contract's witness path names the
//! area it belongs to (`tests::prec::…`) instead of a file.

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(linear_search_in_loop, reason = "1 cost-shape site; #814 lists it")
)]
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(clone_in_loop, reason = "1 cost-shape site; #814 lists it")
)]

extern crate alloc;

#[cfg(test)]
mod algorithms;
#[cfg(test)]
mod prec;
#[cfg(test)]
mod walk;
