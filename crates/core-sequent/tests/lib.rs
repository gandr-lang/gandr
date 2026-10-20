//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::run::…`) instead of a file.

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        allocation_in_repeated_body,
        reason = "1 cost-shape site; #814 lists it"
    )
)]

extern crate alloc;

#[cfg(test)]
mod compare;
#[cfg(test)]
mod differential;
#[cfg(test)]
mod focus_properties;
#[cfg(test)]
mod generate;
#[cfg(test)]
mod run;
