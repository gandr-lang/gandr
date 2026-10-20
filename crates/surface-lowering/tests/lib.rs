//! The integration tests of `gandr-surface-lowering`: one target, each area its
//! own `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        allocation_in_repeated_body,
        reason = "1 cost-shape site; #814 lists it"
    )
)]

extern crate alloc;

#[cfg(test)]
mod modules;
#[cfg(test)]
mod namespace;
#[cfg(test)]
mod recognition;
#[cfg(test)]
mod scopes;
#[cfg(test)]
mod static_operators;
