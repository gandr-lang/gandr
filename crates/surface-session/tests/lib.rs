//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a contract's witness path names the
//! area it belongs to (`tests::session::…`) instead of a file.

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        count_against_constant,
        linear_search_in_loop,
        reason = "3 cost-shape sites (2 linear_search_in_loop, 1 count_against_constant); #814 lists them"
    )
)]

extern crate alloc;

#[cfg(test)]
mod common;
#[cfg(test)]
mod generate;
#[cfg(test)]
mod large;

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
mod forms;
#[cfg(test)]
mod goals;
#[cfg(test)]
mod incremental;
#[cfg(test)]
mod items;
#[cfg(test)]
mod live_match;
#[cfg(test)]
mod pattern_holes;
#[cfg(test)]
mod session;
#[cfg(test)]
mod trial;
#[cfg(test)]
mod written;
