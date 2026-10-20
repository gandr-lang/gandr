//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a contract's witness path names the
//! area it belongs to (`tests::defect::…`) instead of a file.

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        allocation_in_repeated_body,
        reason = "2 cost-shape sites; #814 lists them"
    )
)]

#[cfg(test)]
mod common;

#[cfg(test)]
mod defect;
#[cfg(test)]
mod equations;
#[cfg(test)]
mod keyed;
#[cfg(test)]
mod migrate;
#[cfg(test)]
mod proofs;
#[cfg(test)]
mod schema;
