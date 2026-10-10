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
//! area it belongs to (`tests::session::…`) instead of a file.

#[cfg(test)]
mod common;
#[cfg(test)]
mod generate;

#[cfg(test)]
mod checkpoint;
#[cfg(test)]
mod corpus;
#[cfg(test)]
mod diag;
#[cfg(test)]
mod diag_attr;
#[cfg(test)]
mod diag_obligations;
#[cfg(test)]
mod edit;
#[cfg(test)]
mod goals;
#[cfg(test)]
mod incremental;
#[cfg(test)]
mod items;
#[cfg(test)]
mod session;
