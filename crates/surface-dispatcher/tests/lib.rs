//! The integration tests of `gandr-surface-dispatcher`: one target, each area
//! its own `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(linear_search_in_loop, reason = "1 cost-shape site; #814 lists it")
)]

extern crate alloc;

#[cfg(test)]
mod builtins;
#[cfg(test)]
mod census;
#[cfg(test)]
mod coincide;
#[cfg(test)]
mod corpus;
#[cfg(test)]
mod entries;
#[cfg(test)]
mod parity;
#[cfg(test)]
mod run;
