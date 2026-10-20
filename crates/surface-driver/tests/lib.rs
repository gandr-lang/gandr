//! The integration tests of `gandr-lang`: one target, each area its own
//! `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        allocation_in_repeated_body,
        reason = "2 cost-shape sites; #814 lists them"
    )
)]

#[cfg(test)]
mod cli;
