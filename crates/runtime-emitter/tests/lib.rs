//! The emitter's witnesses, one module per area.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::agreement::…`) instead of a file. The oracle — the
//! named programs, their stated answers and the value-by-value comparison of
//! the two tiers — is the stencils' suite's, shared rather than copied.

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(collect_read_once, reason = "1 cost-shape site; #814 lists it")
)]

extern crate alloc;

#[cfg(test)]
mod agreement;
#[cfg(test)]
mod seam;
#[cfg(test)]
#[path = "../../runtime-stencils/tests/support.rs"]
mod support;
