//! The integration tests of `gandr-theory-decomposition-spaces`: one target,
//! each area its own `cfg(test)` module, so a witness path reads
//! `tests::<area>::<name>`.

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        linear_search_in_loop,
        reverse_after_build,
        reason = "8 cost-shape sites (7 linear_search_in_loop, 1 reverse_after_build); #814 lists them"
    )
)]

#[cfg(test)]
mod composition;
#[cfg(test)]
mod pathway;
