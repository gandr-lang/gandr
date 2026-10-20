//! The integration tests of `gandr-kernel-term`: one target, each area its own
//! `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(clone_in_loop, reason = "1 cost-shape site; #814 lists it")
)]

#[cfg(test)]
mod adversarial_depth;
#[cfg(test)]
mod sharing_format;
