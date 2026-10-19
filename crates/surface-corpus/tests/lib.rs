//! The integration tests of `gandr-surface-corpus`: one target, each area its
//! own `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(count_against_constant, reason = "1 cost-shape site; #814 lists it")
)]

extern crate alloc;

#[cfg(test)]
mod comments;
