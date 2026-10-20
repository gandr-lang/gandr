//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::finite::…`) instead of a file.

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(linear_search_in_loop, reason = "1 cost-shape site; #814 lists it")
)]
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        allocation_in_repeated_body,
        reason = "5 cost-shape sites; #814 lists them"
    )
)]

#[cfg(test)]
mod carriers;
#[cfg(test)]
mod errors;
#[cfg(test)]
mod faces;
#[cfg(test)]
mod finite;
