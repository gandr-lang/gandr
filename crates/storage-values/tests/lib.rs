//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a contract's witness path names the
//! area it belongs to (`tests::values::…`) instead of a file.

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(front_shift_in_loop, reason = "1 cost-shape site; #814 lists it")
)]
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(clone_in_loop, reason = "2 cost-shape sites; #814 lists them")
)]

extern crate alloc;

#[cfg(test)]
mod common;
#[cfg(test)]
mod generate;
#[cfg(test)]
mod reference;

#[cfg(test)]
mod closure;
#[cfg(test)]
mod flat;
#[cfg(test)]
mod frame;
#[cfg(test)]
mod laws;
#[cfg(test)]
mod manifest;
#[cfg(test)]
mod values;
