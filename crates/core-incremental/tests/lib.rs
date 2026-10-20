//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a contract's witness path names the
//! area it belongs to (`tests::incremental::…`) instead of a file.

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        allocation_in_repeated_body,
        reason = "3 cost-shape sites; #814 lists them"
    )
)]

extern crate alloc;

#[cfg(test)]
mod common;
#[cfg(test)]
mod generate;

#[cfg(test)]
mod defects;
#[cfg(test)]
mod incremental;

#[cfg(test)]
mod native_formers;

#[cfg(test)]
mod recursive_data;

#[cfg(test)]
mod supports;
