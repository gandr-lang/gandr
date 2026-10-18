//! The integration tests of `gandr-theory-dynamic-graphs`: one target, each
//! area its own `cfg(test)` module, so a witness path reads
//! `tests::<area>::<name>`. The standing-graph differentials and the
//! offset-regime witnesses run through the public API.

#[cfg(test)]
#[path = "support/differential.rs"]
mod differential;
#[cfg(test)]
#[path = "support/probe.rs"]
mod probe;
#[cfg(test)]
mod standing;
#[cfg(test)]
mod support;
