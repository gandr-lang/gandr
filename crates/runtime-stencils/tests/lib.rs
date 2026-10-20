//! The stencils' witnesses, one module per area.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::agreement::…`) instead of a file.

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        allocation_in_repeated_body,
        reason = "2 cost-shape sites; #814 lists them"
    )
)]

extern crate alloc;

#[cfg(test)]
mod agreement;
#[cfg(test)]
mod exits;
#[cfg(test)]
mod generate;
#[cfg(test)]
mod layout;
#[cfg(test)]
mod support;
