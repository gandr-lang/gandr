// Specification backfill pending (gandr-lang/gandr#9): the executable-
// specification lints are allowed until this crate's own backfill lands.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        spec_attribute_present,
        adequacy_present,
        maybe_shape,
        erased_error_signature
    )
)]
//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a contract's witness path names the
//! area it belongs to (`tests::values::…`) instead of a file.

extern crate alloc;

#[cfg(test)]
mod common;
#[cfg(test)]
mod generate;
#[cfg(test)]
mod reference;

#[cfg(test)]
mod closure;
#[cfg(test)]
mod flat;
#[cfg(test)]
mod frame;
#[cfg(test)]
mod laws;
#[cfg(test)]
mod manifest;
#[cfg(test)]
mod values;
