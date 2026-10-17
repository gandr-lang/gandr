//! The emitter's witnesses, one module per area.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::agreement::…`) instead of a file. The oracle — the
//! named programs and the value-by-value comparison with the L machine — is
//! the stencils' suite's, shared rather than copied.

#[cfg(test)]
mod agreement;
#[cfg(test)]
#[path = "../../runtime-stencils/tests/support.rs"]
mod support;
