//! The integration tests of `gandr-theory-orders`: one target, each area its
//! own `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(front_shift_in_loop, reason = "2 cost-shape sites; #814 lists them")
)]

#[cfg(test)]
mod oracle;
