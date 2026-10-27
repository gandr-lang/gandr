//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a contract's witness path names the
//! area it belongs to (`tests::endpoint::…`) instead of a file.

#[cfg(test)]
mod chunks;
#[cfg(test)]
mod endpoint;
#[cfg(test)]
mod net;
#[cfg(test)]
mod peer;
