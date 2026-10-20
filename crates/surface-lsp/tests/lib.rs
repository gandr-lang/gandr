//! The integration tests of `gandr-surface-lsp`: one target, each area its own
//! `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        spec_clause_traversal,
        reason = "1 clause-cost site (1 spec_clause_traversal, a `String` comparison); #814 lists it"
    )
)]

extern crate alloc;

#[cfg(test)]
mod capabilities;
#[cfg(test)]
mod editor;
#[cfg(test)]
mod session;
