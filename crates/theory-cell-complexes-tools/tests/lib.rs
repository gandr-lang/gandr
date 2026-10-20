//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::inhabitant::…`) instead of a file.

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        allocation_in_repeated_body,
        reason = "1 cost-shape site; #814 lists it"
    )
)]
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(clone_in_loop, reason = "1 cost-shape site; #814 lists it")
)]

#[cfg(test)]
mod adversary;
#[cfg(test)]
mod inhabitant;
#[cfg(test)]
mod workspace;
