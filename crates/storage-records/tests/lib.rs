//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a contract's witness path names the
//! area it belongs to (`tests::membership::…`) instead of a file.

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(linear_search_in_loop, reason = "1 cost-shape site; #814 lists it")
)]

extern crate alloc;

#[cfg(test)]
mod common;

#[cfg(test)]
mod absence;
#[cfg(test)]
mod agreement;
#[cfg(test)]
mod build;
#[cfg(test)]
mod endianness;
#[cfg(test)]
mod membership;
#[cfg(test)]
mod range;
#[cfg(test)]
mod sharing;
#[cfg(test)]
mod store;
