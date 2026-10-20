//! The integration tests of `gandr-surface-diagnostics`: one target, each area
//! its own `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        allocation_in_repeated_body,
        reason = "4 cost-shape sites; #814 lists them"
    )
)]

extern crate alloc;

#[cfg(test)]
mod diagnostics;
