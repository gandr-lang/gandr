//! The emitter's witnesses, one module per area.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::agreement::…`) instead of a file. The oracle — the
//! named programs, their stated answers and the value-by-value comparison of
//! the two tiers — is the stencils' suite's, shared rather than copied, and
//! so are the count's witnesses, which hold the stencils' `dup` and `drop` and
//! this crate's release together.

extern crate alloc;

#[cfg(test)]
mod agreement;
#[cfg(test)]
#[path = "../../runtime-stencils/tests/count.rs"]
mod count;
#[cfg(test)]
mod seam;
#[cfg(test)]
#[path = "../../runtime-stencils/tests/support.rs"]
mod support;
