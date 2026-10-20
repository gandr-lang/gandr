//! The integration tests of `gandr-theory-decomposition-spaces`: one target,
//! each area its own `cfg(test)` module, so a witness path reads
//! `tests::<area>::<name>`.

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        allocation_in_repeated_body,
        reason = "1 cost-shape site; #814 lists it"
    )
)]

#[cfg(test)]
mod composition;
#[cfg(test)]
mod pathway;
