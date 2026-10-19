//! The integration tests of `gandr-surface-repl`: one target, each area its own
//! `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(linear_search_in_loop, reason = "1 cost-shape site; #814 lists it")
)]

#[cfg(test)]
mod live_match;
#[cfg(test)]
mod repl_loop;
